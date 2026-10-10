import OAI.Probability.ContinuumTransition.MeanFieldAttainment

namespace OAI

section
open scoped Topology
open Set Filter
noncomputable section
namespace ContinuumTemperature

def unlift (a : ℝ) (w : Parameter) : Parameter := (w.1-a*w.2^2/2,w.2)

def activeLifts (Q : Parameter → ℝ) (a : ℝ) (P : Parameter → ℝ)
    (x : Parameter) : Set Parameter := {w |
  quadraticCost Q a x w.2 = P x ∧
  SupportOn pressureDomain Q (shiftedField a x w.2) (unlift a w)}

lemma activeLifts_subset {Q P : Parameter → ℝ} {a : ℝ}
    (hP : IsMeanField Q a P) {x : Parameter} (hx : x ∈ pressureDomain) :
    activeLifts Q a P x ⊆ subgradients pressureDomain P x := by
  intro w hw
  have hh := lifted_support hP hx hw.1 (rfl : (unlift a w).2 = w.2) hw.2
  have he : ((unlift a w).1+a*w.2^2/2,w.2) = w := by
    ext <;> dsimp [unlift]; ring
  rw [he] at hh
  exact hh

lemma activeLifts_nonempty {Q P : Parameter → ℝ} {a : ℝ} (ha : 0 < a)
    (hQ : ConvexOn ℝ pressureDomain Q) (hP : IsMeanField Q a P)
    {x : Parameter} (hx : x ∈ pressureDomain)
    (hatt : ∃ d, quadraticCost Q a x d = P x) : (activeLifts Q a P x).Nonempty := by
  obtain ⟨d,hd⟩ := hatt
  obtain ⟨v,hv⟩ := convex_exists_support isOpen_pressureDomain hQ
    (show shiftedField a x d ∈ pressureDomain from hx)
  have he := maximizing_density_eq ha hP hx hd hv
  refine ⟨(v.1+a*d^2/2,d),hd,?_⟩
  convert hv using 1
  ext <;> dsimp [unlift] <;> linarith only [he]

lemma activeLifts_closed_graph {Q P : Parameter → ℝ} {a : ℝ}
    (hQ : ContinuousOn Q pressureDomain) (hP : ContinuousOn P pressureDomain)
    {X V : ℕ → Parameter} {x v : Parameter} (hx : x ∈ pressureDomain)
    (hX : Tendsto X atTop (𝓝 x)) (hV : Tendsto V atTop (𝓝 v))
    (hXS : ∀ n, X n ∈ pressureDomain) (hA : ∀ n, V n ∈ activeLifts Q a P (X n)) :
    v ∈ activeLifts Q a P x := by
  have hshift : Tendsto (fun n => shiftedField a (X n) (V n).2) atTop
      (𝓝 (shiftedField a x v.2)) :=
    (show Continuous (fun p : Parameter × Parameter => shiftedField a p.1 p.2.2) by unfold shiftedField; fun_prop).tendsto
      (x,v) |>.comp (hX.prodMk_nhds hV)
  have hunlift : Tendsto (fun n => unlift a (V n)) atTop (𝓝 (unlift a v)) :=
    (show Continuous (unlift a) by unfold unlift; fun_prop).tendsto v |>.comp hV
  have hQlim : Tendsto (fun n => Q (shiftedField a (X n) (V n).2)) atTop
      (𝓝 (Q (shiftedField a x v.2))) :=
    (hQ (shiftedField a x v.2) (show shiftedField a x v.2 ∈ pressureDomain from hx)).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hshift,Eventually.of_forall (fun n => show shiftedField a (X n) (V n).2 ∈ pressureDomain from hXS n)⟩)
  have hPlim := (hP x hx).tendsto.comp
    (tendsto_nhdsWithin_iff.2 ⟨hX,Eventually.of_forall hXS⟩)
  have hquad : Tendsto (fun n => (X n).1*a*(V n).2^2/2) atTop (𝓝 (x.1*a*v.2^2/2)) := by
    exact ((((continuous_fst.tendsto x).comp hX).mul_const a).mul (((continuous_snd.tendsto v).comp hV).pow 2)).div_const 2
  constructor
  · exact tendsto_nhds_unique ((hQlim.sub hquad).congr (fun n => (hA n).1)) hPlim
  · exact supportOn_limit hQ (show shiftedField a x v.2 ∈ pressureDomain from hx) hshift hunlift (Eventually.of_forall hXS)
      (Eventually.of_forall fun n => (hA n).2)

lemma meanField_subgradients {Q P : Parameter → ℝ} {a : ℝ} (ha : 0 < a)
    (hQ : ConvexOn ℝ pressureDomain Q) (hP : IsMeanField Q a P)
    (hatt : ∀ x ∈ pressureDomain, ∃ d, quadraticCost Q a x d = P x)
    {x : Parameter} (hx : x ∈ pressureDomain) :
    subgradients pressureDomain P x = closedConvexHull ℝ (activeLifts Q a P x) := by
  have hc := meanField_convex hQ hP
  exact support_generators_closedHull isOpen_pressureDomain hc (activeLifts Q a P)
    (fun _ hx => activeLifts_subset hP hx)
    (fun _ hx => activeLifts_nonempty ha hQ hP hx (hatt _ hx))
    (fun hx hX hV hXS hA => activeLifts_closed_graph (hQ.continuousOn isOpen_pressureDomain)
      (hc.continuousOn isOpen_pressureDomain) hx hX hV hXS hA) hx

lemma support_density_nonneg {Q : Parameter → ℝ}
    (hm : ∀ β, 0 < β → Monotone (fun h => Q (β,h))) {x v : Parameter}
    (hx : x ∈ pressureDomain) (hv : SupportOn pressureDomain Q x v) : 0 ≤ v.2 := by
  have hh := hv (x.1,x.2-1) hx
  have hl := hm x.1 hx (show x.2-1 ≤ x.2 by linarith)
  dsimp [pDot] at hh
  simpa only [Prod.mk.eta] using (show 0 ≤ v.2 by linarith)

lemma active_density_nonneg {Q P : Parameter → ℝ} {a : ℝ}
    (hm : ∀ β, 0 < β → Monotone (fun h => Q (β,h))) {x w : Parameter}
    (hx : x ∈ pressureDomain) (hw : w ∈ activeLifts Q a P x) : 0 ≤ w.2 :=
  support_density_nonneg (v := unlift a w) hm (show shiftedField a x w.2 ∈ pressureDomain from hx) hw.2

lemma active_canonical_eq {Q P : Parameter → ℝ} {H : ℝ → ℝ → ℝ} {a : ℝ}
    (hH : IsPartialConjugate Q H)
    (hm : ∀ β, 0 < β → Monotone (fun h => Q (β,h))) {x w : Parameter}
    (hx : x ∈ pressureDomain) (hw : w ∈ activeLifts Q a P x) :
    P x = x.2*w.2+x.1*a*w.2^2/2-H x.1 w.2 := by
  have hd := active_density_nonneg hm hx hw
  have he := fenchel_eq_of_support hH hx hd (supports_iff_supportOn.mpr hw.2)
  have hlow := hw.1
  dsimp [shiftedField,unlift,quadraticCost] at he hlow
  nlinarith only [he,hlow]

end ContinuumTemperature
end
end

end OAI
