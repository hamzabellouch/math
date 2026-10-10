import Mathlib
import OAI.Probability.JammingConcavity.CylinderSecants

namespace OAI

/-! Parabolic Interior. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open Set Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory Filter Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open scoped NNReal ENNReal Topology
open scoped NNReal Topology
open Set
open Set Filter MeasureTheory
open Set Filter
open scoped Topology

namespace MicroscopicJamming

 

lemma backward_comparison_interior {Q K C : ℝ} (hQ : 0 < Q) (hK : 0 ≤ K) (hC : 0 ≤ C)
    {U b d : ℝ → ℝ → ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℝ => U p.1 p.2) (Icc 0 Q ×ˢ univ))
    (hx : ∀ t ∈ Icc 0 Q, Differentiable ℝ (U t) ∧ Differentiable ℝ (deriv (U t)))
    (ht : ∀ t ∈ Ioo 0 Q, ∀ x, HasDerivAt (fun s => U s x) (d t x) t)
    (hb : ∀ t ∈ Icc 0 Q, ∀ x, |b t x| ≤ K*(1+|x|))
    (hg : ∀ t ∈ Icc 0 Q, ∀ x, U t x ≤ C*(1+x^2))
    (hp : ∀ t ∈ Ioo 0 Q, ∀ x,
      0 ≤ d t x+(1/2:ℝ)*deriv (deriv (U t)) x+b t x*deriv (U t) x)
    (hterm : ∀ x, U Q x ≤ 0) :
    ∀ t ∈ Icc 0 Q, ∀ x, U t x ≤ 0 := by
  have hint (t : ℝ) (ht' : t ∈ Ioo 0 Q) (x : ℝ) : U t x ≤ 0 := by
    have hlen : 0 < Q-t := sub_pos.mpr ht'.2
    have hshift (s : ℝ) (hs : s ∈ Icc 0 (Q-t)) : s+t ∈ Icc 0 Q := by
      constructor <;> linarith [hs.1,hs.2,ht'.1]
    have hshift' (s : ℝ) (hs : s ∈ Ico 0 (Q-t)) : s+t ∈ Ioo 0 Q := by
      constructor <;> linarith [hs.1,hs.2,ht'.1]
    have hcc : ContinuousOn (fun p : ℝ × ℝ => U (p.1+t) p.2) (Icc 0 (Q-t) ×ˢ univ) := by
      apply hc.comp
        (show ContinuousOn (fun p : ℝ × ℝ => (p.1+t,p.2)) (Icc 0 (Q-t) ×ˢ univ) from
          (by fun_prop))
      intro p hp'
      exact ⟨hshift p.1 hp'.1,mem_univ _⟩
    have htime (s : ℝ) (hs : s ∈ Ico 0 (Q-t)) (y : ℝ) :
        HasDerivWithinAt (fun r => U (r+t) y) (d (s+t) y) (Ici s) s := by
      exact ((ht (s+t) (hshift' s hs) y).comp_add_const s t).hasDerivWithinAt
    have hh := backward_comparison (Q-t) K C hlen hK hC
      (fun s y => U (s+t) y) (fun s y => b (s+t) y) (fun s y => d (s+t) y)
      hcc (fun s hs => hx (s+t) (hshift s hs)) htime
      (fun s hs => hb (s+t) (hshift s hs)) (fun s hs => hg (s+t) (hshift s hs))
      (fun s hs => hp (s+t) (hshift' s hs)) (by simpa using hterm)
      0 ⟨le_rfl,hlen.le⟩ x
    simpa using hh
  intro t ht' x
  have hc' : ContinuousOn (fun s => U s x) (Icc 0 Q) :=
    hc.comp (continuous_id.prodMk continuous_const).continuousOn (fun s hs => ⟨hs,mem_univ _⟩)
  have he : closure (Ioo (0:ℝ) Q)=Icc 0 Q := closure_Ioo hQ.ne
  apply le_on_closure (fun s hs => hint s hs x)
    (he ▸ hc') continuousOn_const
  rwa [he]
end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming

lemma row_classical_variance_le {Q : ℝ} {u m : ℝ → ℝ} {F G : ℝ → ℝ → ℝ}
    (hQ : 0 < Q) (hm : ∀ t ∈ Icc 0 Q, 0 ≤ m t ∧ m t ≤ 1)
    (hF : RowClassicalVarianceSolution Q u m F) (hG : RowClassicalVarianceSolution Q u m G) :
    ∀ t ∈ Icc 0 Q, ∀ x, F t x ≤ G t x := by
  obtain ⟨hcF,hxcF,hxxcF,hxF,htF,htermF,KF,hKF,hboundF⟩ := hF
  obtain ⟨hcG,hxcG,hxxcG,hxG,htG,htermG,KG,hKG,hboundG⟩ := hG
  let U : ℝ → ℝ → ℝ := fun t x => F t x-G t x
  let b : ℝ → ℝ → ℝ := fun t x => m t*(deriv (F t) x+deriv (G t) x)/2
  let d : ℝ → ℝ → ℝ := fun t x =>
    -(1/2:ℝ)*(deriv (deriv (F t)) x+m t*(deriv (F t) x)^2)-
    (-(1/2:ℝ)*(deriv (deriv (G t)) x+m t*(deriv (G t) x)^2))
  have hdx (t : ℝ) (ht : t ∈ Icc 0 Q) (x : ℝ) :
      HasDerivAt (U t) (deriv (F t) x-deriv (G t) x) x :=
    ((hxF t ht).1 x).hasDerivAt.sub ((hxG t ht).1 x).hasDerivAt
  have hdx2 (t : ℝ) (ht : t ∈ Icc 0 Q) (x : ℝ) :
      HasDerivAt (deriv (U t)) (deriv (deriv (F t)) x-deriv (deriv (G t)) x) x := by
    have he : deriv (U t)=fun y => deriv (F t) y-deriv (G t) y :=
      funext fun y => (hdx t ht y).deriv
    rw [he]
    exact ((hxF t ht).2 x).hasDerivAt.sub ((hxG t ht).2 x).hasDerivAt
  have hc : ContinuousOn (fun p : ℝ × ℝ => U p.1 p.2) (Icc 0 Q ×ˢ univ) := hcF.sub hcG
  have hx (t : ℝ) (ht : t ∈ Icc 0 Q) :
      Differentiable ℝ (U t) ∧ Differentiable ℝ (deriv (U t)) :=
    ⟨fun x => (hdx t ht x).differentiableAt,fun x => (hdx2 t ht x).differentiableAt⟩
  have htime (t : ℝ) (ht : t ∈ Ioo 0 Q) (x : ℝ) :
      HasDerivAt (fun s => U s x) (d t x) t := (htF t ht x).sub (htG t ht x)
  have hb (t : ℝ) (ht : t ∈ Icc 0 Q) (x : ℝ) : |b t x| ≤ (KF+KG)*(1+|x|) := by
    have hsum : |deriv (F t) x+deriv (G t) x| ≤ (KF+KG)*(1+|x|) := by
      calc
        _ ≤ |deriv (F t) x|+|deriv (G t) x| := abs_add_le _ _
        _ ≤ KF*(1+|x|)+KG*(1+|x|) := add_le_add (hboundF t ht x).2 (hboundG t ht x).2
        _ = _ := by ring
    have hnon : 0 ≤ (KF+KG)*(1+|x|) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hsum (hm t ht).1
    have hmul' := mul_le_mul_of_nonneg_right (hm t ht).2 hnon
    dsimp [b]
    rw [abs_div,abs_mul,abs_of_nonneg (hm t ht).1,abs_of_pos (by norm_num : (0:ℝ)<2)]
    linarith
  have hg (t : ℝ) (ht : t ∈ Icc 0 Q) (x : ℝ) : U t x ≤ (KF+KG)*(1+x^2) := by
    dsimp [U]
    have h1 := (hboundF t ht x).1
    have h2 := (hboundG t ht x).1
    nlinarith [le_abs_self (F t x),neg_abs_le (G t x)]
  have hp (t : ℝ) (ht : t ∈ Ioo 0 Q) (x : ℝ) :
      0 ≤ d t x+(1/2:ℝ)*deriv (deriv (U t)) x+b t x*deriv (U t) x := by
    rw [(hdx2 t ⟨ht.1.le,ht.2.le⟩ x).deriv,(hdx t ⟨ht.1.le,ht.2.le⟩ x).deriv]
    dsimp [d,b]
    ring_nf
    exact le_rfl
  have hterm (x : ℝ) : U Q x ≤ 0 := by simp [U,htermF x,htermG x]
  have hh := backward_comparison_interior hQ (add_nonneg hKF hKG) (add_nonneg hKF hKG)
    hc hx htime hb hg hp hterm
  intro t ht x
  exact sub_nonpos.mp (hh t ht x)

def RowVarianceUniquenessStatement : Prop :=
  ∀ (Q : ℝ) (u m : ℝ → ℝ), 0 < Q → ContinuousOn m (Icc 0 Q) →
    (∀ t ∈ Icc 0 Q, 0 ≤ m t ∧ m t ≤ 1) →
    ∀ F G : ℝ → ℝ → ℝ,
      RowClassicalVarianceSolution Q u m F → RowClassicalVarianceSolution Q u m G →
      ∀ t ∈ Icc 0 Q, ∀ x, F t x=G t x

theorem row_variance_uniqueness : RowVarianceUniquenessStatement := by
  intro Q u m hQ _ hm F G hF hG t ht x
  exact le_antisymm (row_classical_variance_le hQ hm hF hG t ht x)
    (row_classical_variance_le hQ hm hG hF t ht x)
end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming
 

theorem row_variance_existence : RowVarianceExistenceStatement := by
  intro A B C κ Q hQ hA hC hκ hκQ
  obtain ⟨D,L,hD,hL,hpath⟩ := gaussian_step_path A B C κ Q hQ hA hC hκ hκQ
  refine ⟨L,hL,?_⟩
  intro u hu m hm hmb
  have hLn (rs : ℕ → List (ℝ × ℝ))
      (hrs : ∀ n, ∀ r ∈ rs n, 0 ≤ r.1 ∧ r.1 ≤ 1 ∧ 0 ≤ r.2)
      (hT : ∀ n, gaussianStepTime (rs n)=Q)
      (n : ℕ) (t : ℝ) (ht : t ∈ Icc 0 Q) (x : ℝ) :
      |deriv (gaussianStepPath (rs n) u t) x| ≤ L*(1+|x|) :=
    ((hpath u hu (rs n) (hrs n) (hT n).le).2.2.2 t ht.1 (by rw [hT]; exact ht.2)).2.2 x |>.1
  obtain ⟨rs,hrs,hT,hrm⟩ := exists_gaussian_grid_approximation hQ hm hmb
  obtain ⟨F,hF,hb,hconv⟩ := gaussian_classical_limit hQ hu hL hrs hT hm hrm (hLn rs hrs hT)
  refine ⟨F,hF,hb,?_,?_⟩
  · intro G hG
    exact row_variance_uniqueness Q u m hQ hm hmb F G hF hG
  · intro ss hss hS hsm
    obtain ⟨G,hG,_,hGconv⟩ := gaussian_classical_limit hQ hu hL hss hS hm hsm (hLn ss hss hS)
    intro R hR
    exact (hGconv R hR).congr_right (fun p hp =>
      (row_variance_uniqueness Q u m hQ hm hmb F G hF hG p.1 hp.1 p.2).symm)
end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming
 

def RowSmoothProfile (Q : ℝ) (q : ℝ → ℝ) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) q ∧ q 0=0 ∧ q 1=Q ∧
    ∀ s ∈ Icc (0:ℝ) 1, 0 < deriv q s

def RowClassicalRankSolution (u q : ℝ → ℝ) (f : ℝ → ℝ → ℝ) : Prop :=
  ContinuousOn (fun p : ℝ × ℝ => f p.1 p.2) (Icc 0 1 ×ˢ univ) ∧
  ContinuousOn (fun p : ℝ × ℝ => deriv (f p.1) p.2) (Icc 0 1 ×ˢ univ) ∧
  ContinuousOn (fun p : ℝ × ℝ => deriv (deriv (f p.1)) p.2) (Icc 0 1 ×ˢ univ) ∧
  (∀ s ∈ Icc (0:ℝ) 1, Differentiable ℝ (f s) ∧ Differentiable ℝ (deriv (f s))) ∧
  (∀ s ∈ Ioo (0:ℝ) 1, ∀ x, HasDerivAt (fun r => f r x)
    (-(deriv q s)/2*(deriv (deriv (f s)) x+s*(deriv (f s) x)^2)) s) ∧
  (∀ x, f 1 x=u x) ∧
  ∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ Icc (0:ℝ) 1, ∀ x,
    |f s x| ≤ K*(1+x^2) ∧ |deriv (f s) x| ≤ K*(1+|x|)

 

def RowParameterStatement : Prop :=
  ∀ (u q η : ℝ → ℝ) (A B C κ Q : ℝ), 0 < Q →
    RowAnalyticTerminal u A B C κ Q → RowSmoothProfile Q q →
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) η → η 0=0 → η 1=0 →
  ∃ r : ℝ, 0 < r ∧ ∃ f : ℝ → ℝ → ℝ → ℝ,
    (∀ ε, |ε| < r → RowClassicalRankSolution u (fun s => q s+ε*η s) (f ε)) ∧
    (∀ n : ℕ, ∀ s ∈ Icc (0:ℝ) 1, ∀ x : ℝ,
      DifferentiableAt ℝ (fun ε => iteratedDeriv n (f ε s) x) 0 ∧
      DifferentiableAt ℝ (deriv (fun ε => iteratedDeriv n (f ε s) x)) 0)
end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming
lemma RowSmoothProfile.strictMonoOn {Q : ℝ} {q : ℝ → ℝ}
    (hq : RowSmoothProfile Q q) : StrictMonoOn q (Icc (0:ℝ) 1) :=
  strictMonoOn_of_deriv_pos (convex_Icc _ _) hq.1.continuous.continuousOn
    (fun s hs => hq.2.2.2 s (interior_subset hs))
lemma RowSmoothProfile.mapsTo {Q : ℝ} {q : ℝ → ℝ}
    (hq : RowSmoothProfile Q q) : MapsTo q (Icc (0:ℝ) 1) (Icc 0 Q) := by
  intro s hs
  constructor
  · simpa only [hq.2.1] using hq.strictMonoOn.monotoneOn (by norm_num : (0:ℝ) ∈ Icc 0 1) hs hs.1
  · simpa only [hq.2.2.1] using hq.strictMonoOn.monotoneOn hs (by norm_num : (1:ℝ) ∈ Icc 0 1) hs.2
lemma RowSmoothProfile.mapsTo_open {Q : ℝ} {q : ℝ → ℝ}
    (hq : RowSmoothProfile Q q) : MapsTo q (Ioo (0:ℝ) 1) (Ioo 0 Q) := by
  intro s hs
  constructor
  · simpa only [hq.2.1] using hq.strictMonoOn (by norm_num : (0:ℝ) ∈ Icc 0 1) (Ioo_subset_Icc_self hs) hs.1
  · simpa only [hq.2.2.1] using hq.strictMonoOn (Ioo_subset_Icc_self hs) (by norm_num : (1:ℝ) ∈ Icc 0 1) hs.2

 

lemma rowSmooth_inverse {Q : ℝ} {q : ℝ → ℝ} (hq : RowSmoothProfile Q q) :
    ∃ m : ℝ → ℝ, ContinuousOn m (Icc 0 Q) ∧
      (∀ t ∈ Icc 0 Q, 0 ≤ m t ∧ m t ≤ 1) ∧
      (∀ t ∈ Icc 0 Q, q (m t)=t) ∧
      (∀ s ∈ Icc (0:ℝ) 1, m (q s)=s) := by
  let f : Icc (0:ℝ) 1 → Icc (0:ℝ) Q := fun s => ⟨q s,hq.mapsTo s.property⟩
  have hf : Continuous f := by
    exact (hq.1.continuous.comp continuous_subtype_val).subtype_mk _
  have hbij : Function.Bijective f := by
    constructor
    · intro s t hst
      exact Subtype.ext (hq.strictMonoOn.injOn s.property t.property (congrArg Subtype.val hst))
    · intro t
      have him : t.val ∈ Icc (q 0) (q 1) := by simpa only [hq.2.1,hq.2.2.1] using t.property
      obtain ⟨s,hs,he⟩ := intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1) hq.1.continuous.continuousOn him
      exact ⟨⟨s,hs⟩,Subtype.ext he⟩
  let e : Icc (0:ℝ) 1 ≃ₜ Icc (0:ℝ) Q :=
    (Equiv.ofBijective f hbij).toHomeomorphOfContinuousClosed hf hf.isClosedMap
  let m : ℝ → ℝ := fun t => if ht : t ∈ Icc 0 Q then (e.symm ⟨t,ht⟩).val else 0
  have hm (t : ℝ) (ht : t ∈ Icc 0 Q) : m t=(e.symm ⟨t,ht⟩).val := dite_eq_left ht
  refine ⟨m,?_,?_,?_,?_⟩
  · rw [continuousOn_iff_continuous_domRestrict]
    exact (continuous_subtype_val.comp e.symm.continuous).congr (fun t => (hm t t.property).symm)
  · intro t ht
    rw [hm t ht]
    exact (e.symm ⟨t,ht⟩).property
  · intro t ht
    rw [hm t ht]
    exact congrArg Subtype.val (e.apply_symm_apply ⟨t,ht⟩)
  · intro s hs
    rw [hm (q s) (hq.mapsTo hs)]
    exact congrArg Subtype.val (e.symm_apply_apply ⟨s,hs⟩)

lemma rowSmooth_inverse_hasDerivAt {Q : ℝ} {q m : ℝ → ℝ}
    (hq : RowSmoothProfile Q q) (hm : ContinuousOn m (Icc 0 Q))
    (hmb : ∀ t ∈ Icc 0 Q, 0 ≤ m t ∧ m t ≤ 1)
    (hinv : ∀ t ∈ Icc 0 Q, q (m t)=t) {t : ℝ} (ht : t ∈ Ioo 0 Q) :
    HasDerivAt m (deriv q (m t))⁻¹ t := by
  apply HasDerivAt.of_local_left_inverse (hm.continuousAt (Icc_mem_nhds ht.1 ht.2))
    (((hq.1.differentiable (by simp)) (m t)).hasDerivAt)
    (hq.2.2.2 (m t) (hmb t (Ioo_subset_Icc_self ht))).ne'
  exact Filter.mem_of_superset (Icc_mem_nhds ht.1 ht.2) (fun s hs => hinv s hs)
end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming
lemma rowVariance_to_rank {Q : ℝ} {u q m : ℝ → ℝ}
    (hq : RowSmoothProfile Q q) (hinv : ∀ s ∈ Icc (0:ℝ) 1, m (q s)=s)
    {F : ℝ → ℝ → ℝ} (hF : RowClassicalVarianceSolution Q u m F) :
    RowClassicalRankSolution u q (fun s => F (q s)) := by
  rcases hF with ⟨hc,hc1,hc2,hx,ht,hterm,K,hK,hgrowth⟩
  have hp : ContinuousOn (fun p : ℝ × ℝ => (q p.1,p.2)) (Icc 0 1 ×ˢ univ) :=
    ((hq.1.continuous.comp continuous_fst).prodMk continuous_snd).continuousOn
  have hmap : MapsTo (fun p : ℝ × ℝ => (q p.1,p.2)) (Icc 0 1 ×ˢ univ) (Icc 0 Q ×ˢ univ) :=
    fun p hpp => ⟨hq.mapsTo hpp.1,mem_univ _⟩
  refine ⟨hc.comp hp hmap,hc1.comp hp hmap,hc2.comp hp hmap,
    (fun s hs => hx (q s) (hq.mapsTo hs)),?_,?_,K,hK,?_⟩
  · intro s hs x
    have hds := (hq.1.differentiable (by simp) s).hasDerivAt
    have hh := (ht (q s) (hq.mapsTo_open hs) x).comp s hds
    rw [hinv s (Ioo_subset_Icc_self hs)] at hh
    convert hh using 1 <;> first | rfl | (dsimp; ring)
  · intro x
    change F (q 1) x=u x
    rw [hq.2.2.1]
    exact hterm x
  · intro s hs x
    exact hgrowth (q s) (hq.mapsTo hs) x

lemma rowSmooth_inverse_mapsTo_open {Q : ℝ} {q m : ℝ → ℝ}
    (hq : RowSmoothProfile Q q)
    (hmb : ∀ t ∈ Icc 0 Q, 0 ≤ m t ∧ m t ≤ 1)
    (hinv : ∀ t ∈ Icc 0 Q, q (m t)=t) :
    MapsTo m (Ioo 0 Q) (Ioo (0:ℝ) 1) := by
  intro t ht
  have hcc := Ioo_subset_Icc_self ht
  have hb := hmb t hcc
  constructor
  · apply lt_of_le_of_ne hb.1
    intro he
    have hg := hinv t hcc
    rw [←he,hq.2.1] at hg
    linarith [ht.1]
  · apply lt_of_le_of_ne hb.2
    intro he
    have hg := hinv t hcc
    rw [he,hq.2.2.1] at hg
    linarith [ht.2]

lemma rowRank_to_variance {Q : ℝ} {u q m : ℝ → ℝ}
    (hq : RowSmoothProfile Q q) (hm : ContinuousOn m (Icc 0 Q))
    (hmb : ∀ t ∈ Icc 0 Q, 0 ≤ m t ∧ m t ≤ 1)
    (hinv : ∀ t ∈ Icc 0 Q, q (m t)=t)
    (hleft : ∀ s ∈ Icc (0:ℝ) 1, m (q s)=s)
    {f : ℝ → ℝ → ℝ} (hf : RowClassicalRankSolution u q f) :
    RowClassicalVarianceSolution Q u m (fun t => f (m t)) := by
  rcases hf with ⟨hc,hc1,hc2,hx,ht,hterm,K,hK,hgrowth⟩
  have hp : ContinuousOn (fun p : ℝ × ℝ => (m p.1,p.2)) (Icc 0 Q ×ˢ univ) :=
    (hm.comp continuousOn_fst (fun p hp => hp.1)).prodMk continuousOn_snd
  have hmap : MapsTo (fun p : ℝ × ℝ => (m p.1,p.2)) (Icc 0 Q ×ˢ univ) (Icc 0 1 ×ˢ univ) :=
    fun p hpp => ⟨hmb p.1 hpp.1,mem_univ _⟩
  refine ⟨hc.comp hp hmap,hc1.comp hp hmap,hc2.comp hp hmap,
    (fun s hs => hx (m s) (hmb s hs)),?_,?_,K,hK,?_⟩
  · intro t htt x
    have hh := (ht (m t) (rowSmooth_inverse_mapsTo_open hq hmb hinv htt) x).comp t
      (rowSmooth_inverse_hasDerivAt hq hm hmb hinv htt)
    have hn : deriv q (m t) ≠ 0 := (hq.2.2.2 (m t) (hmb t (Ioo_subset_Icc_self htt))).ne'
    convert hh using 1 <;> first | rfl | (dsimp; field_simp [hn])
  · intro x
    have h1 : m Q=1 := by simpa only [hq.2.2.1] using hleft 1 (by norm_num)
    change f (m Q) x=u x
    rw [h1]
    exact hterm x
  · intro t htt x
    exact hgrowth (m t) (hmb t htt) x

 

lemma row_rank_existence_unique {A B C κ Q : ℝ} {u q : ℝ → ℝ}
    (hQ : 0<Q) (hu : RowAnalyticTerminal u A B C κ Q) (hq : RowSmoothProfile Q q) :
    ∃ f : ℝ → ℝ → ℝ, RowClassicalRankSolution u q f ∧
      (∀ s ∈ Icc (0:ℝ) 1, ∀ x, -C ≤ deriv (deriv (f s)) x ∧
        deriv (deriv (f s)) x ≤ κ/(1-κ*(Q-q s))) ∧
      (∀ g : ℝ → ℝ → ℝ, RowClassicalRankSolution u q g →
        ∀ s ∈ Icc (0:ℝ) 1, ∀ x, f s x=g s x) := by
  obtain ⟨m,hm,hmb,hinv,hleft⟩ := rowSmooth_inverse hq
  obtain ⟨L,hL,hsolve⟩ := row_variance_existence A B C κ Q hQ hu.2.1 hu.2.2.1 hu.2.2.2.1 hu.2.2.2.2.1
  obtain ⟨F,hF,hbound,hunique,_⟩ := hsolve u hu m hm hmb
  refine ⟨fun s => F (q s),rowVariance_to_rank hq hleft hF,?_,?_⟩
  · intro s hs x
    exact (hbound (q s) (hq.mapsTo hs) x).2.2.2
  · intro g hg s hs x
    have hh := hunique (fun t => g (m t)) (rowRank_to_variance hq hm hmb hinv hleft hg) (q s) (hq.mapsTo hs) x
    simpa only [hleft s hs] using hh
end MicroscopicJamming

 
open Set Filter
open scoped Topology

namespace MicroscopicJamming

lemma backward_reaction_source_upper {Q K R H S : ℝ} (hQ : 0 < Q) (hK : 0 ≤ K) (hR : 0 ≤ R) (hH : 0 ≤ H) (hS : 0 ≤ S)
    {U b d r : ℝ → ℝ → ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℝ => U p.1 p.2) (Icc 0 Q ×ˢ univ))
    (hx : ∀ t ∈ Icc 0 Q, Differentiable ℝ (U t) ∧ Differentiable ℝ (deriv (U t)))
    (ht : ∀ t ∈ Ico 0 Q, ∀ x, HasDerivWithinAt (fun s => U s x) (d t x) (Ici t) t)
    (hb : ∀ t ∈ Icc 0 Q, ∀ x, |b t x| ≤ K*(1+|x|))
    (hg : Higher.UniformPolynomialGrowth (Icc 0 Q) U)
    (hr : ∀ t ∈ Ico 0 Q, ∀ x, r t x ≤ R)
    (hp : ∀ t ∈ Ico 0 Q, ∀ x,
      -S ≤ d t x+(1/2:ℝ)*deriv (deriv (U t)) x+b t x*deriv (U t) x+r t x*U t x)
    (hterm : ∀ x, U Q x ≤ H) :
    ∀ t ∈ Icc 0 Q, ∀ x, U t x ≤ (H+S*(Q-t))*Real.exp (R*(Q-t)) := by
  let E : ℝ → ℝ := fun t => Real.exp (R*(t-Q))
  let V : ℝ → ℝ → ℝ := fun t x => E t*U t x-(H+S*(Q-t))
  let vd : ℝ → ℝ → ℝ := fun t x => E t*(d t x+R*U t x)+S
  have hE (t : ℝ) : HasDerivAt E (R*E t) t := by
    convert (((hasDerivAt_id t).sub_const Q).const_mul R).exp using 1 <;> first | rfl | (dsimp [E]; ring)
  have hEc : Continuous E := continuous_iff_continuousAt.mpr (fun t => (hE t).continuousAt)
  have hEp (t : ℝ) : 0 < E t := Real.exp_pos _
  have hEl (t : ℝ) (ht' : t ∈ Icc 0 Q) : E t ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos hR (sub_nonpos.mpr ht'.2))
  have hvx (t : ℝ) (ht' : t ∈ Icc 0 Q) (x : ℝ) :
      HasDerivAt (V t) (E t*deriv (U t) x) x :=
    (((hx t ht').1 x).hasDerivAt.const_mul (E t)).sub_const (H+S*(Q-t))
  have hvxx (t : ℝ) (ht' : t ∈ Icc 0 Q) (x : ℝ) :
      HasDerivAt (deriv (V t)) (E t*deriv (deriv (U t)) x) x := by
    have he : deriv (V t)=fun y => E t*deriv (U t) y := funext (fun y => (hvx t ht' y).deriv)
    rw [he]
    exact ((hx t ht').2 x).hasDerivAt.const_mul (E t)
  have hvtime (t : ℝ) (ht' : t ∈ Ico 0 Q) (x : ℝ) :
      HasDerivWithinAt (fun s => V s x) (vd t x) (Ici t) t := by
    have hW : HasDerivAt (fun s : ℝ => H+S*(Q-s)) (-S) t := by
      convert (HasDerivAt.const_add H (((hasDerivAt_const t Q).sub (hasDerivAt_id t)).const_mul S)) using 1 <;> first | rfl | ring
    convert ((hE t).hasDerivWithinAt.mul (ht t ht' x)).sub hW.hasDerivWithinAt using 1;
      first | rfl | (dsimp [vd]; ring)
  have hWnon (t : ℝ) (ht' : t ∈ Icc 0 Q) : 0 ≤ H+S*(Q-t) := by
    have := sub_nonneg.mpr ht'.2
    positivity
  have hWle (t : ℝ) (ht' : t ∈ Icc 0 Q) : H+S*(Q-t) ≤ H+S*Q := by nlinarith [ht'.1]
  have hvg : Higher.UniformPolynomialGrowth (Icc 0 Q) V := by
    obtain ⟨n,C,hC,hg⟩ := hg
    refine ⟨n,C+H+S*Q,by positivity,fun t ht' x => ?_⟩
    have he := mul_le_mul_of_nonneg_right (hEl t ht') (abs_nonneg (U t x))
    have hp1 : 1 ≤ (1+|x|)^n := one_le_pow₀ (by linarith [abs_nonneg x])
    calc
      |V t x| ≤ |E t*U t x|+|H+S*(Q-t)| := abs_sub _ _
      _ = E t*|U t x|+(H+S*(Q-t)) := by rw [abs_mul,abs_of_pos (hEp t),abs_of_nonneg (hWnon t ht')]
      _ ≤ |U t x|+(H+S*Q) := by simpa only [one_mul] using add_le_add he (hWle t ht')
      _ ≤ C*(1+|x|)^n+(H+S*Q)*(1+|x|)^n :=
        add_le_add (hg t ht' x) (le_mul_of_one_le_right (by positivity) hp1)
      _ = _ := by ring
  have hvc : ContinuousOn (fun p : ℝ × ℝ => V p.1 p.2) (Icc 0 Q ×ˢ univ) :=
    ((hEc.comp continuous_fst).continuousOn.mul hc).sub
      (continuousOn_const.add (continuousOn_const.mul (continuousOn_const.sub continuousOn_fst)))
  have hcomp := backward_polynomial_comparison hQ hK hvc
    (fun t ht' => ⟨fun x => (hvx t ht' x).differentiableAt,fun x => (hvxx t ht' x).differentiableAt⟩)
    hvtime hb hvg (fun t ht' x hpos => ?_) (fun x => ?_)
  · intro t ht' x
    have h := hcomp t ht' x
    dsimp [V] at h
    have hexp : E t*Real.exp (R*(Q-t))=1 := by rw [← Real.exp_add]; convert Real.exp_zero using 1; congr 1; ring
    have hh := mul_le_mul_of_nonneg_right (show E t*U t x ≤ H+S*(Q-t) by linarith) (Real.exp_nonneg (R*(Q-t)))
    calc
      U t x = (E t*Real.exp (R*(Q-t)))*U t x := by rw [hexp,one_mul]
      _ = E t*U t x*Real.exp (R*(Q-t)) := by ring
      _ ≤ _ := hh
  · rw [(hvxx t ⟨ht'.1,ht'.2.le⟩ x).deriv,(hvx t ⟨ht'.1,ht'.2.le⟩ x).deriv]
    have hpp := hp t ht' x
    have hrp := hr t ht' x
    have hUp : 0 ≤ E t*U t x := by dsimp [V] at hpos; linarith [hWnon t ⟨ht'.1,ht'.2.le⟩]
    have hnn := mul_nonneg (sub_nonneg.mpr hrp) hUp
    dsimp [vd]
    calc
      _ = E t*(d t x+(1/2:ℝ)*deriv (deriv (U t)) x+b t x*deriv (U t) x+r t x*U t x)+
          (R-r t x)*(E t*U t x)+S := by ring
      _ ≥ 0 := by
        have hh := mul_le_mul_of_nonneg_left hpp (hEp t).le
        have he := mul_le_mul_of_nonneg_right (hEl t ⟨ht'.1,ht'.2.le⟩) hS
        nlinarith
  · dsimp [V,E]
    simp only [sub_self,mul_zero,Real.exp_zero,one_mul,add_zero]
    exact sub_nonpos.mpr (hterm x)

lemma backward_reaction_source_bound {Q K R H S : ℝ} (hQ : 0 < Q) (hK : 0 ≤ K) (hR : 0 ≤ R) (hH : 0 ≤ H) (hS : 0 ≤ S)
    {U b d r : ℝ → ℝ → ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℝ => U p.1 p.2) (Icc 0 Q ×ˢ univ))
    (hx : ∀ t ∈ Icc 0 Q, Differentiable ℝ (U t) ∧ Differentiable ℝ (deriv (U t)))
    (ht : ∀ t ∈ Ico 0 Q, ∀ x, HasDerivWithinAt (fun s => U s x) (d t x) (Ici t) t)
    (hb : ∀ t ∈ Icc 0 Q, ∀ x, |b t x| ≤ K*(1+|x|))
    (hg : Higher.UniformPolynomialGrowth (Icc 0 Q) U)
    (hr : ∀ t ∈ Ico 0 Q, ∀ x, r t x ≤ R)
    (hp : ∀ t ∈ Ico 0 Q, ∀ x,
      |d t x+(1/2:ℝ)*deriv (deriv (U t)) x+b t x*deriv (U t) x+r t x*U t x| ≤ S)
    (hterm : ∀ x, |U Q x| ≤ H) :
    ∀ t ∈ Icc 0 Q, ∀ x, |U t x| ≤ (H+S*(Q-t))*Real.exp (R*(Q-t)) := by
  have hupper := backward_reaction_source_upper hQ hK hR hH hS hc hx ht hb hg hr (fun t ht x => (abs_le.mp (hp t ht x)).1)
    (fun x => (le_abs_self _).trans (hterm x))
  have hn1 (t : ℝ) (ht' : t ∈ Icc 0 Q) : deriv (fun x => -U t x)=fun x => -deriv (U t) x := by
    funext x; exact ((hx t ht').1 x).hasDerivAt.neg.deriv
  have hn2 (t : ℝ) (ht' : t ∈ Icc 0 Q) : deriv (deriv (fun x => -U t x))=fun x => -deriv (deriv (U t)) x := by
    rw [hn1 t ht']; funext x; exact ((hx t ht').2 x).hasDerivAt.neg.deriv
  have hneg := backward_reaction_source_upper (U:=fun t x => -U t x) (d:=fun t x => -d t x)
    hQ hK hR hH hS hc.neg
    (fun t ht' => ⟨(hx t ht').1.neg,by rw [hn1 t ht']; exact (hx t ht').2.neg⟩)
    (fun t ht' x => (ht t ht' x).neg) hb
    (by simpa only [neg_one_mul] using hg.const_mul (-1)) hr
    (fun t ht' x => by rw [hn2 t ⟨ht'.1,ht'.2.le⟩,hn1 t ⟨ht'.1,ht'.2.le⟩]; linarith [(abs_le.mp (hp t ht' x)).2])
    (fun x => (neg_le_abs _).trans (hterm x))
  intro t ht' x
  rw [abs_le]
  exact ⟨by linarith [hneg t ht' x],hupper t ht' x⟩

lemma forward_reaction_source_bound {Q K R H S : ℝ} (hQ : 0 < Q) (hK : 0 ≤ K) (hR : 0 ≤ R) (hH : 0 ≤ H) (hS : 0 ≤ S)
    {U b d r : ℝ → ℝ → ℝ}
    (hc : ContinuousOn (fun p : ℝ × ℝ => U p.1 p.2) (Icc 0 Q ×ˢ univ))
    (hx : ∀ t ∈ Icc 0 Q, Differentiable ℝ (U t) ∧ Differentiable ℝ (deriv (U t)))
    (ht : ∀ t ∈ Ioc 0 Q, ∀ x, HasDerivAt (fun s => U s x) (d t x) t)
    (hb : ∀ t ∈ Icc 0 Q, ∀ x, |b t x| ≤ K*(1+|x|))
    (hg : Higher.UniformPolynomialGrowth (Icc 0 Q) U)
    (hr : ∀ t ∈ Ioc 0 Q, ∀ x, r t x ≤ R)
    (hp : ∀ t ∈ Ioc 0 Q, ∀ x,
      |d t x-(1/2:ℝ)*deriv (deriv (U t)) x-b t x*deriv (U t) x-r t x*U t x| ≤ S)
    (hterm : ∀ x, |U 0 x| ≤ H) :
    ∀ t ∈ Icc 0 Q, ∀ x, |U t x| ≤ (H+S*t)*Real.exp (R*t) := by
  have hm (t : ℝ) (ht' : t ∈ Icc 0 Q) : Q-t ∈ Icc 0 Q :=
    ⟨by linarith [ht'.2],by linarith [ht'.1]⟩
  have hmo (t : ℝ) (ht' : t ∈ Ico 0 Q) : Q-t ∈ Ioc 0 Q :=
    ⟨by linarith [ht'.2],by linarith [ht'.1]⟩
  have hvc : ContinuousOn (fun p : ℝ × ℝ => U (Q-p.1) p.2) (Icc 0 Q ×ˢ univ) :=
    hc.comp (show ContinuousOn (fun p : ℝ × ℝ => (Q-p.1,p.2)) _ by fun_prop)
      (fun p hp' => ⟨hm p.1 hp'.1,mem_univ _⟩)
  have hvt (t : ℝ) (ht' : t ∈ Ico 0 Q) (x : ℝ) :
      HasDerivWithinAt (fun s => U (Q-s) x) (-d (Q-t) x) (Ici t) t := by
    convert ((ht (Q-t) (hmo t ht') x).comp t ((hasDerivAt_const t Q).sub (hasDerivAt_id t))).hasDerivWithinAt using 1 <;>
      first | rfl | ring
  have hcomp := backward_reaction_source_bound (U:=fun t => U (Q-t)) (b:=fun t => b (Q-t))
    (d:=fun t x => -d (Q-t) x) (r:=fun t => r (Q-t)) hQ hK hR hH hS hvc
    (fun t ht' => hx (Q-t) (hm t ht')) hvt (fun t ht' => hb (Q-t) (hm t ht'))
    (hg.comp (fun t ht' => hm t ht')) (fun t ht' => hr (Q-t) (hmo t ht'))
    (fun t ht' x => by
      have he : -d (Q-t) x+(1/2:ℝ)*deriv (deriv (U (Q-t))) x+b (Q-t) x*deriv (U (Q-t)) x+r (Q-t) x*U (Q-t) x =
          -(d (Q-t) x-(1/2:ℝ)*deriv (deriv (U (Q-t))) x-b (Q-t) x*deriv (U (Q-t)) x-r (Q-t) x*U (Q-t) x) := by ring
      rw [he,abs_neg]
      exact hp (Q-t) (hmo t ht') x)
    (fun x => by simpa using hterm x)
  intro t ht' x
  simpa only [sub_sub_cancel] using hcomp (Q-t) (hm t ht') x

end MicroscopicJamming

end

end OAI
