import Mathlib
import OAI.GroupTheory.SimpleAmenable.RandomFields.FlagAveragingMatrices
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.GoodRowSeparators

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section FlagTentMass
open Classical

noncomputable def flagRowTent {a m D : ℕ} {v : ℝ×ℝ} (s t : ℝ)
    (z w : FlagSite a m D v) : ℝ :=
  if z.val.1=w.val.1 then planeTent s (flagSiteOrdinary z) (flagSiteOrdinary w)*
    planeTent t (flagSiteConjugate z) (flagSiteConjugate w) else 0

noncomputable def latticeRowTent (D : ℕ) (s t : ℝ) (x y : ℝ×ℝ) (u : CutRing×CutRing) : ℝ :=
  planeTent s x (scaledOrdinary D u)*planeTent t y (scaledConjugate D u)

noncomputable def tentRowOffset (s t : ℝ) (x y : ℝ×ℝ) : (Fin 2 → ℝ)×(Fin 2 → ℝ) :=
  (![-x.1/s,-y.1/t],![-x.2/s,-y.2/t])

theorem latticeRowTent_eq (D : ℕ) (s t : ℝ) (x y : ℝ×ℝ) (u : CutRing×CutRing) :
    latticeRowTent D s t x y u=
      pairedUnitTent (tentRowOffset s t x y+pairedQuadraticEmbedding D s t u) := by
  simp only [latticeRowTent,planeTent,scaledOrdinary,scaledConjugate,pairedUnitTent,
    doubleUnitTent,Fin.prod_univ_two,unitTent,tentRowOffset,pairedQuadraticEmbedding,
    LinearMap.prodMap_apply,quadraticScaledEmbedding,LinearMap.coe_mk,AddHom.coe_mk,
    Prod.fst_add,Prod.snd_add,Pi.add_apply,Matrix.cons_val_zero,Matrix.cons_val_one]
  have h (a b d c : ℝ) : |(a-b/d)/c|=|-a/c+b/(d*c)| := by
    have he : -a/c+b/(d*c) = -((a-b/d)/c) := by rw [div_mul_eq_div_div]; ring
    rw [he,abs_neg]
  rw [h,h,h,h]
  ring

theorem squareBoundary_of_interior {v x : ℝ×ℝ}
    (hx : 0<x.1 ∧ x.1<1 ∧ 0<x.2 ∧ x.2<1) : SquareBoundary v x := by
  exact ⟨⟨hx.1.le,hx.2.1.le⟩,⟨hx.2.2.1.le,hx.2.2.2.le⟩,
    (fun h => (ne_of_gt hx.1 h).elim),(fun h => (ne_of_lt hx.2.1 h).elim),
    (fun h => (ne_of_gt hx.2.2.1 h).elim),(fun h => (ne_of_lt hx.2.2.2 h).elim)⟩

noncomputable def flagSiteFromNumerator {a m D : ℕ} {v : ℝ×ℝ}
    (hv : TransverseDirection a v) (k : Fin m) (u : CutRing×CutRing)
    (hu : SquareBoundary v (scaledOrdinary D u)) : FlagSite a m D v :=
  ⟨(k,⟨scaledOrdinary D u,hv,hu⟩),u,rfl⟩

@[simp] theorem flagSiteFromNumerator_numerator {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (hv : TransverseDirection a v) (k : Fin m) (u : CutRing×CutRing)
    (hu : SquareBoundary v (scaledOrdinary D u)) :
    flagSiteNumerator (flagSiteFromNumerator hv k u hu)=u :=
  scaledOrdinary_injective hD (flagSiteNumerator_spec _)

theorem flagSiteFromNumerator_conjugate {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    (hv : TransverseDirection a v) (k : Fin m) (u : CutRing×CutRing)
    (hu : SquareBoundary v (scaledOrdinary D u)) :
    flagSiteConjugate (flagSiteFromNumerator hv k u hu)=scaledConjugate D u := by
  simp [flagSiteConjugate,flagSiteFromNumerator_numerator hD]

theorem latticeRowTent_interior {a m D : ℕ} {v : ℝ×ℝ} {s t : ℝ} (hs : 0<s)
    (z : FlagSite a m D v)
    (hi : s<(flagSiteOrdinary z).1 ∧ (flagSiteOrdinary z).1<1-s ∧
      s<(flagSiteOrdinary z).2 ∧ (flagSiteOrdinary z).2<1-s)
    (u : CutRing×CutRing)
    (hu : latticeRowTent D s t (flagSiteOrdinary z) (flagSiteConjugate z) u≠0) :
    SquareBoundary v (scaledOrdinary D u) := by
  have hh := (planeTent_ne_zero hs _ _).mp (mul_ne_zero_iff.mp hu).1
  have hx := abs_lt.mp hh.1
  have hy := abs_lt.mp hh.2
  apply squareBoundary_of_interior
  exact ⟨by linarith [hi.1],by linarith [hi.2.1],by linarith [hi.2.2.1],by linarith [hi.2.2.2]⟩

theorem flagRowTent_lattice_sum {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    {s t : ℝ} (hs : 0<s) (ht : 0<t) (z : FlagSite a m D v)
    (hi : s<(flagSiteOrdinary z).1 ∧ (flagSiteOrdinary z).1<1-s ∧
      s<(flagSiteOrdinary z).2 ∧ (flagSiteOrdinary z).2<1-s)
    (S : Finset (CutRing×CutRing))
    (hS : ∀u,u∉S → latticeRowTent D s t (flagSiteOrdinary z) (flagSiteConjugate z) u=0) :
    ∃T : Finset (FlagSite a m D v),
      (∀w,w∉T → flagRowTent s t z w=0) ∧
      (∑w∈T,flagRowTent s t z w)=
        ∑u∈S,latticeRowTent D s t (flagSiteOrdinary z) (flagSiteConjugate z) u := by
  let R := |(flagSiteConjugate z).1|+|(flagSiteConjugate z).2|+t
  have hR : 0<R := by dsimp [R]; positivity
  let T := (flagSiteBox_finite (a:=a) (m:=m) (v:=v) hD hR).toFinset
  have hn (w : FlagSite a m D v) (hw : flagRowTent s t z w≠0) :
      z.val.1=w.val.1 ∧ latticeRowTent D s t (flagSiteOrdinary z) (flagSiteConjugate z)
        (flagSiteNumerator w)≠0 := by
    have he : z.val.1=w.val.1 := by
      by_contra hh
      exact hw (by simp [flagRowTent,hh])
    refine ⟨he,?_⟩
    simpa only [flagRowTent,ite_eq_left he,latticeRowTent,flagSiteNumerator_spec,
      flagSiteOrdinary,flagSiteConjugate] using hw
  have hT (w : FlagSite a m D v) (hw : flagRowTent s t z w≠0) : w∈T := by
    have hh := (planeTent_ne_zero ht _ _).mp (mul_ne_zero_iff.mp (hn w hw).2).2
    have hx : |(flagSiteConjugate w).1| < |(flagSiteConjugate z).1|+t := by
      have h := abs_add_le ((flagSiteConjugate w).1-(flagSiteConjugate z).1) (flagSiteConjugate z).1
      rw [sub_add_cancel,abs_sub_comm] at h
      have hh₁ : |(flagSiteConjugate z).1-(flagSiteConjugate w).1| < t := hh.1
      linarith
    have hy : |(flagSiteConjugate w).2| < |(flagSiteConjugate z).2|+t := by
      have h := abs_add_le ((flagSiteConjugate w).2-(flagSiteConjugate z).2) (flagSiteConjugate z).2
      rw [sub_add_cancel,abs_sub_comm] at h
      have hh₂ : |(flagSiteConjugate z).2-(flagSiteConjugate w).2| < t := hh.2
      linarith
    apply (Set.Finite.mem_toFinset _).mpr
    exact ⟨by dsimp [R]; linarith [abs_nonneg (flagSiteConjugate z).2],
      by dsimp [R]; linarith [abs_nonneg (flagSiteConjugate z).1]⟩
  refine ⟨T,fun w hw => by by_contra hh; exact hw (hT w hh),?_⟩
  apply Finset.sum_bij_ne_zero (fun w _ _ => flagSiteNumerator w)
  · intro w hw hnz
    exact by_contra (fun hh => (hn w hnz).2 (hS _ hh))
  · intro w hw hnw w' hw' hnw' he
    apply Subtype.ext
    apply Prod.ext
    · exact (hn w hnw).1.symm.trans (hn w' hnw').1
    · apply Subtype.ext
      rw [← flagSiteNumerator_spec w,← flagSiteNumerator_spec w',he]
  · intro u hu hnu
    let w := flagSiteFromNumerator z.val.2.property.1 z.val.1 u (latticeRowTent_interior hs z hi u hnu)
    have he : flagRowTent s t z w=latticeRowTent D s t (flagSiteOrdinary z) (flagSiteConjugate z) u := by
      rw [flagRowTent,ite_eq_left (show z.val.1=w.val.1 from rfl)]
      change planeTent s _ (scaledOrdinary D u)*planeTent t _ (flagSiteConjugate (flagSiteFromNumerator _ _ _ _)) = _
      rw [flagSiteFromNumerator_conjugate hD]
      rfl
    have hw : flagRowTent s t z w≠0 := by rwa [he]
    exact ⟨w,hT w hw,hw,flagSiteFromNumerator_numerator hD _ _ _ _⟩
  · intro w hw hnw
    simp only [flagRowTent,ite_eq_left (hn w hnw).1,latticeRowTent,
      flagSiteNumerator_spec,flagSiteOrdinary,flagSiteConjugate]

theorem flagRowTent_mass {a m D : ℕ} {v : ℝ×ℝ} (hD : 0<D)
    {s t : ℝ} (hs : 0<s) (ht : 0<t) (hst : 36 ≤ s*t) (z : FlagSite a m D v)
    (hi : s<(flagSiteOrdinary z).1 ∧ (flagSiteOrdinary z).1<1-s ∧
      s<(flagSiteOrdinary z).2 ∧ (flagSiteOrdinary z).2<1-s) :
    ∃T : Finset (FlagSite a m D v),
      (∀w,w∉T → flagRowTent s t z w=0) ∧
      |(5/((D:ℝ)^4*s^2*t^2))*(∑w∈T,flagRowTent s t z w)-1| ≤
        38880/((D:ℝ)*Real.sqrt (s*t)) := by
  obtain ⟨S,hS,hh⟩ := pairedQuadratic_tent_mass (d:=D) (by exact_mod_cast hD) hs ht hst
    (tentRowOffset s t (flagSiteOrdinary z) (flagSiteConjugate z))
  simp only [← latticeRowTent_eq] at hS hh
  obtain ⟨T,hT,he⟩ := flagRowTent_lattice_sum hD hs ht z hi S hS
  exact ⟨T,hT,by rwa [he]⟩

end FlagTentMass

section FiniteDifference

theorem finiteDifference_lipschitz {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (θ : E → ℝ) (hθ : Differentiable ℝ θ) {L : NNReal}
    (hL : LipschitzWith L (fderiv ℝ θ)) (δ x y : E) :
    |(θ (x+δ)-θ x)-(θ (y+δ)-θ y)| ≤ (L:ℝ)*‖δ‖*‖x-y‖ := by
  let F : E → ℝ := fun x => θ (x+δ)-θ x
  have hf (x : E) : HasFDerivAt F (fderiv ℝ θ (x+δ)-fderiv ℝ θ x) x := by
    have hh := (hasFDerivAt_comp_add_right δ).mpr (hθ (x+δ)).hasFDerivAt
    exact hh.sub (hθ x).hasFDerivAt
  have hb (z : E) : ‖fderiv ℝ F z‖ ≤ (L:ℝ)*‖δ‖ := by
    rw [(hf z).fderiv]
    simpa only [add_sub_cancel_left] using hL.norm_sub_le (z+δ) z
  have hh := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜:=ℝ)
    (f:=F) (s:=Set.univ) (fun z _ => (hf z).differentiableAt) (fun z _ => hb z)
    convex_univ (Set.mem_univ y) (Set.mem_univ x)
  simpa only [F,Real.norm_eq_abs] using hh

theorem compactSignal_uniform_constants {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ψ : E → ℝ) (hψ : ContDiff ℝ 2 ψ) (hs : HasCompactSupport ψ) :
    ∃L₀ L₁ : NNReal,LipschitzWith L₀ ψ ∧ ∀δ x y : E,
      |(ψ (x+δ)-ψ x)-(ψ (y+δ)-ψ y)| ≤ (L₁:ℝ)*‖δ‖*‖x-y‖ := by
  obtain ⟨L₀,hL₀⟩ := hψ.lipschitzWith_of_hasCompactSupport hs (by norm_num)
  have hd : ContDiff ℝ 1 (fderiv ℝ ψ) := hψ.fderiv_right (by norm_num)
  obtain ⟨L₁,hL₁⟩ := hd.lipschitzWith_of_hasCompactSupport (hs.fderiv ℝ) (by norm_num)
  exact ⟨L₀,L₁,hL₀,finiteDifference_lipschitz ψ (hψ.differentiable (by norm_num)) hL₁⟩

end FiniteDifference

end SimpleAmenable
end
end

end OAI
