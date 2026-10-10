import Mathlib
import OAI.Analysis.Commutator.FreeCreation

namespace OAI

noncomputable section

section

open scoped ComplexOrder InnerProductSpace

noncomputable section

namespace Kadison

open Filter _root_.Topology

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

def zeroLimitSpace (F : ℕ → H →L[ℂ] H) : Submodule ℂ H where
  carrier := {x | Tendsto (fun n => F n x) atTop (𝓝 0)}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change Tendsto (fun n => F n (x+y)) atTop (𝓝 0)
    simpa only [map_add, add_zero] using hx.add hy
  smul_mem' := by
    intro c x hx
    change Tendsto (fun n => F n (c • x)) atTop (𝓝 0)
    simpa only [map_smul, smul_zero] using hx.const_smul c

lemma zeroLimitSpace_closed (F : ℕ → H →L[ℂ] H) (hb : ∀ n, ‖F n‖ ≤ 1) :
    IsClosed (zeroLimitSpace F : Set H) := by
  have hF : Equicontinuous (fun n x => F n x) :=
    (LipschitzWith.uniformEquicontinuous (fun n x => F n x) 1
      (fun n => (F n).lipschitzWith.weaken (by exact_mod_cast hb n))).equicontinuous
  exact hF.isClosed_setOfPred_tendsto continuous_const

end Kadison

namespace Kadison.FreeCreation

open FreeMoments FreeWordTensor Filter _root_.Topology

attribute [local instance] Classical.propDecidable

open scoped InnerProductSpace

open UniformSpace

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable (hfree : Free S t.functional.toLinearMap)

include hfree in
lemma tailProjection_mul_tail {i : ι} {a : A} (ha : a ∈ S i)
    {x : t.functional.GNS} (hx : x ∈ tailSpace t S i) :
    (tailSpace t S i).starProjection (t.functional.gnsStarAlgHom a x) =
      t.functional a • x := by
  let c := a - t.functional a • (1 : A)
  have hc : c ∈ S i := sub_mem ha (SMulMemClass.smul_mem _ (one_mem _))
  have hc0 : t.functional c = 0 := by simp [c, t.normalized]
  have hcx := headSpace_le_tailSpace_orthogonal t S hfree i
    (creation_mem_headSpace t S i hc hc0 hx)
  have hp : (tailSpace t S i).starProjection (t.functional.gnsStarAlgHom c x) = 0 := by
    simp only [Submodule.starProjection_apply,
      Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal hcx, ZeroMemClass.coe_zero]
  have heq : t.functional.gnsStarAlgHom c x =
      t.functional.gnsStarAlgHom a x - t.functional a • x := by
    simp [c]
  rw [heq, map_sub, map_smul, (tailSpace t S i).starProjection_eq_self_iff.mpr hx] at hp
  exact sub_eq_zero.mp hp

include hfree in
lemma tailProjection_mul_centered_tail {i : ι} {a : A} (ha : a ∈ S i)
    (ha0 : t.functional a=0) {x : t.functional.GNS} (hx : x ∈ tailSpace t S i) :
    (tailSpace t S i).starProjection (t.functional.gnsStarAlgHom a x)=0 := by
  rw [tailProjection_mul_tail t S hfree ha hx, ha0, zero_smul]

include hfree in
lemma norm_tailProjection_mul (i : ι) {a : A} (ha : a ∈ S i) :
    ‖(tailSpace t S i).starProjection * t.functional.gnsStarAlgHom a‖ ≤
      ‖t.functional.toPreGNS (star a)‖ := by
  have hn : ‖t.functional.gnsStarAlgHom (star a) * (tailSpace t S i).starProjection‖ ≤
      ‖t.functional.toPreGNS (star a)‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    change ‖t.functional.gnsStarAlgHom (star a) ((tailSpace t S i).starProjection x)‖ ≤ _
    rw [norm_mul_tailSpace t S hfree i (star_mem ha)
      ((tailSpace t S i).starProjection_apply_mem x)]
    exact mul_le_mul_of_nonneg_left ((tailSpace t S i).norm_starProjection_apply_le x)
      (norm_nonneg _)
  have heq : star (t.functional.gnsStarAlgHom (star a) * (tailSpace t S i).starProjection) =
      (tailSpace t S i).starProjection * t.functional.gnsStarAlgHom a := by
    rw [star_mul, (isSelfAdjoint_starProjection _).star_eq, ← map_star, star_star]
  rw [← heq, norm_star]
  exact hn

lemma wordVector_mem_tail {i : ι} {w : List (Letter t S)}
    (hw : Reduced w) (hi : CanPrepend t S i w) :
    wordVector t S w ∈ tailSpace t S i :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨w, hw, hi, rfl⟩)

include hfree in
lemma tailProjection_mul_word (i : ι) {a : A} (ha : a ∈ S i)
    (ha0 : t.functional a=0) {w : List (Letter t S)} (hw : Reduced w) :
    (tailSpace t S i).starProjection (t.functional.gnsStarAlgHom a (wordVector t S w)) =
      match w with
      | [] => 0
      | b :: z => if b.color=i then t.functional (a*b.val) • wordVector t S z else 0 := by
  cases w with
  | nil =>
      exact tailProjection_mul_centered_tail t S hfree ha ha0
        (wordVector_mem_tail t S reduced_nil (by simp [CanPrepend]))
  | cons b z =>
    change _ = if b.color=i then t.functional (a*b.val) • wordVector t S z else 0
    by_cases hb : b.color=i
    · rw [ite_eq_left hb]
      have hz : CanPrepend t S i z := by
        cases z with
        | nil => simp [CanPrepend]
        | cons c z =>
          have := hw.rel
          simpa [CanPrepend, hb] using this
      have heq : t.functional.gnsStarAlgHom a (wordVector t S (b::z)) =
          t.functional.gnsStarAlgHom (a*b.val) (wordVector t S z) := by
        simp only [mul_wordVector, word_cons, mul_assoc]
      rw [heq]
      exact tailProjection_mul_tail t S hfree
        (mul_mem ha (by simpa [hb] using b.mem)) (wordVector_mem_tail t S hw.tail hz)
    · rw [ite_eq_right hb]
      exact tailProjection_mul_centered_tail t S hfree ha ha0
        (wordVector_mem_tail t S hw (by simpa [CanPrepend] using Ne.symm hb))

include hfree in
theorem tailProjection_mul_tendsto_zero (i : ι) (x : ℕ → A)
    (hx : ∀ n, x n ∈ S i) (hx0 : ∀ n, t.functional (x n)=0)
    (hbound : ∀ n, ‖t.functional.toPreGNS (star (x n))‖ ≤ 1)
    (hmoment : ∀ a ∈ S i, Tendsto (fun n => t.functional (x n*a)) atTop (𝓝 0))
    (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
      Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))
    (y : t.functional.GNS) :
    Tendsto (fun n => (tailSpace t S i).starProjection (t.functional.gnsStarAlgHom (x n) y))
      atTop (𝓝 0) := by
  let F : ℕ → t.functional.GNS →L[ℂ] t.functional.GNS :=
    fun n => (tailSpace t S i).starProjection * t.functional.gnsStarAlgHom (x n)
  let P := zeroLimitSpace F
  have hP : IsClosed (P : Set t.functional.GNS) :=
    zeroLimitSpace_closed F (fun n => (norm_tailProjection_mul t S hfree i (hx n)).trans (hbound n))
  have hw : ∀ w : List (Letter t S), Reduced w → wordVector t S w ∈ P := by
    intro w hw
    change Tendsto _ _ _
    simp only [F, mul_apply_eq_comp,
      tailProjection_mul_word t S hfree i (hx _) (hx0 _) hw]
    cases w with
    | nil => exact tendsto_const_nhds
    | cons b z =>
      by_cases hb : b.color=i
      · simp only [ite_eq_left hb]
        simpa only [zero_smul] using
          (hmoment b.val (by simpa [hb] using b.mem)).smul_const (wordVector t S z)
      · simp only [ite_eq_right hb]
        exact tendsto_const_nhds
  have hg : ∀ a ∈ iSup S, (t.functional.toPreGNS a : t.functional.GNS) ∈ P := by
    intro a ha
    have ha' : a ∈ FreeMoments.wordSpan S t.functional.toLinearMap := by
      change a ∈ (FreeMoments.reducedAlgebra S (fun a => map_star t.functional a) t.normalized)
      rw [FreeMoments.reducedAlgebra_eq_iSup]
      exact ha
    clear ha
    induction ha' using Submodule.span_induction with
    | mem a ha => obtain ⟨w, hr, rfl⟩ := ha; exact hw w hr
    | zero => simp only [map_zero, Completion.coe_zero, Submodule.zero_mem]
    | add a b _ _ ha hb => simpa only [map_add, Completion.coe_add] using P.add_mem ha hb
    | smul c a _ ha => simpa only [map_smul, Completion.coe_smul] using P.smul_mem c ha
  have hall : ∀ z : t.functional.GNS, z ∈ P := by
    intro z
    induction z using Completion.induction_on with
    | hp => exact hP
    | ih z =>
      let ξ : t.functional.GNS := (t.functional.toPreGNS 1 : t.functional.GNS)
      have hz := Kadison.bicommutant_mem_cyclicSubspace (generatedOperators t S)
        (hgen (t.functional.ofPreGNS z)) ξ
      have heq : t.functional.gnsStarAlgHom (t.functional.ofPreGNS z) ξ =
          (z : t.functional.GNS) := by
        simp [ξ, PositiveLinearMap.gnsStarAlgHom]
      rw [heq] at hz
      apply closure_minimal (s := (Kadison.orbitSubmodule (generatedOperators t S) ξ : Set _))
        ?_ hP hz
      rintro f ⟨a, ha, rfl⟩
      obtain ⟨b, hb, rfl⟩ := ha
      simpa [ξ, PositiveLinearMap.gnsStarAlgHom] using hg b hb
  exact hall y

end Kadison.FreeCreation

namespace Kadison.FreeCreation

open FreeMoments FreeWordTensor Filter _root_.Topology

open scoped InnerProductSpace

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable (hfree : Free S t.functional.toLinearMap)

include hfree in
lemma mul_head_norm {i j : ι} (hij : i ≠ j) {a : A} (ha : a ∈ S j)
    (ha0 : t.functional a=0) (ha1 : ‖t.functional.toPreGNS a‖=1)
    {y : t.functional.GNS} (hy : y ∈ headSpace t S i) :
    t.functional.gnsStarAlgHom a y ∈ headSpace t S j ∧
      ‖t.functional.gnsStarAlgHom a y‖=‖y‖ := by
  have ht := headSpace_le_other_tailSpace t S hij hy
  exact ⟨creation_mem_headSpace t S j ha ha0 ht,
    by rw [norm_mul_tailSpace t S hfree j ha ht, ha1, one_mul]⟩

include hfree in
lemma repeated_prefix_head {i j : ι} (hij : i ≠ j) {x s : A}
    (hx : x ∈ S i) (hx0 : t.functional x=0) (hx1 : ‖t.functional.toPreGNS x‖=1)
    (hs : s ∈ S j) (hs0 : t.functional s=0) (hs1 : ‖t.functional.toPreGNS s‖=1)
    (k : ℕ) {y : t.functional.GNS} (hy : y ∈ headSpace t S i) :
    t.functional.gnsStarAlgHom ((s*x)^k*s) y ∈ headSpace t S j ∧
      ‖t.functional.gnsStarAlgHom ((s*x)^k*s) y‖=‖y‖ := by
  induction k with
  | zero => simpa using mul_head_norm t S hfree hij hs hs0 hs1 hy
  | succ k ih =>
    have h1 := mul_head_norm t S hfree hij.symm hx hx0 hx1 ih.1
    have h2 := mul_head_norm t S hfree hij hs hs0 hs1 h1.1
    have heq : t.functional.gnsStarAlgHom ((s*x)^(k+1)*s) y =
        t.functional.gnsStarAlgHom s (t.functional.gnsStarAlgHom x
          (t.functional.gnsStarAlgHom ((s*x)^k*s) y)) := by
      simp only [pow_succ', mul_assoc, map_mul, mul_apply_eq_comp]
    rw [heq]
    exact ⟨h2.1, h2.2.trans (h1.2.trans ih.2)⟩

include hfree in
lemma prefix_split_bound {i j : ι} (hij : i ≠ j) {x s : A}
    (hx : x ∈ S i) (hx0 : t.functional x=0) (hx1 : ‖t.functional.toPreGNS x‖=1)
    (hs : s ∈ S j) (hs0 : t.functional s=0) (hs1 : ‖t.functional.toPreGNS s‖=1)
    (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
      Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))
    (k : ℕ) (y : t.functional.GNS) :
    ‖t.functional.gnsStarAlgHom ((s*x)^k*s) y‖ ≤ ‖y‖ +
      ‖(s*x)^k*s‖ * ‖(tailSpace t S i).starProjection y‖ := by
  let P := (tailSpace t S i).starProjection
  let L := t.functional.gnsStarAlgHom ((s*x)^k*s)
  have hhead : y-P y ∈ headSpace t S i := by
    rw [headSpace_eq_tailSpace_orthogonal t S hfree i hgen]
    exact (tailSpace t S i).sub_starProjection_mem_orthogonal y
  have hi := (repeated_prefix_head t S hfree hij hx hx0 hx1 hs hs0 hs1 k hhead).2
  have hnorm : ‖y-P y‖ ≤ ‖y‖ := by
    have h := ((tailSpace t S i)ᗮ).norm_starProjection_apply_le y
    simpa only [Submodule.starProjection_orthogonal', sub_apply, one_apply_eq_self] using h
  calc
    ‖L y‖ = ‖L (y-P y)+L (P y)‖ := by rw [← map_add, sub_add_cancel]
    _ ≤ ‖L (y-P y)‖+‖L (P y)‖ := norm_add_le _ _
    _ ≤ ‖y‖+‖L‖*‖P y‖ := add_le_add (hi.le.trans hnorm) (L.le_opNorm _)
    _ ≤ ‖y‖+‖(s*x)^k*s‖*‖P y‖ := by
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right
        (NonUnitalStarAlgHom.norm_apply_le t.functional.gnsStarAlgHom _) (norm_nonneg _))

include hfree in
theorem repeated_prefix_eventual_bound {i j : ι} (hij : i ≠ j)
    (x : ℕ → A) (s : A)
    (hx : ∀ n, x n ∈ S i) (hx0 : ∀ n, t.functional (x n)=0)
    (hx1 : ∀ n, ‖t.functional.toPreGNS (x n)‖=1)
    (hxs : ∀ n, ‖t.functional.toPreGNS (star (x n))‖≤1)
    (hs : s ∈ S j) (hs0 : t.functional s=0) (hs1 : ‖t.functional.toPreGNS s‖=1)
    (hmoment : ∀ a ∈ S i, Tendsto (fun n => t.functional (x n*a)) atTop (𝓝 0))
    (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
      Set.centralizer (Set.centralizer (generatedOperators t S : Set _)))
    (k : ℕ) (M : ℝ) (hM : ∀ n, ‖(s*x n)^k*s‖≤M)
    (y : t.functional.GNS) (η : ℝ) (hη : 0<η) :
    ∀ᶠ n in atTop, ‖t.functional.gnsStarAlgHom ((s*x n)^k*s)
        (t.functional.gnsStarAlgHom (x n) y)‖ ≤
      ‖t.functional.gnsStarAlgHom (x n) y‖+η := by
  have hz := tailProjection_mul_tendsto_zero t S hfree i x hx hx0 hxs hmoment hgen y
  have hz' : Tendsto (fun n => M*‖(tailSpace t S i).starProjection
      (t.functional.gnsStarAlgHom (x n) y)‖) atTop (𝓝 0) := by
    simpa only [norm_zero, mul_zero] using hz.norm.const_mul M
  have he : ∀ᶠ n in atTop, M*‖(tailSpace t S i).starProjection
      (t.functional.gnsStarAlgHom (x n) y)‖<η := hz'.eventually_lt_const hη
  filter_upwards [he] with n hn
  exact (prefix_split_bound t S hfree hij (hx n) (hx0 n) (hx1 n) hs hs0 hs1 hgen k _).trans
    (add_le_add le_rfl ((mul_le_mul_of_nonneg_right (hM n) (norm_nonneg _)).trans hn.le))

end Kadison.FreeCreation

namespace Kadison.FreeCreation

open FreeWordTensor

open scoped InnerProductSpace

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A)

lemma norm_mul_supported (x q : A) (c : ℝ) (hc : 0≤c)
    (hxx : star x*x=(c : ℂ) • q) (y : t.functional.GNS)
    (hy : t.functional.gnsStarAlgHom q y=y) :
    ‖t.functional.gnsStarAlgHom x y‖=Real.sqrt c*‖y‖ := by
  have hi := ContinuousLinearMap.adjoint_inner_right (t.functional.gnsStarAlgHom x) y
    (t.functional.gnsStarAlgHom x y)
  change inner ℂ y ((star (t.functional.gnsStarAlgHom x)*t.functional.gnsStarAlgHom x) y) = _ at hi
  rw [←map_star, ←map_mul, hxx, map_smul, smul_apply, hy, inner_smul_right,
    inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at hi
  have hr := congrArg Complex.re hi
  have heq : c*‖y‖^2=‖t.functional.gnsStarAlgHom x y‖^2 := by
    simpa only [RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow,
      ←Complex.ofReal_mul, Complex.ofReal_re] using hr
  have hs := Real.sq_sqrt hc
  have hpos := mul_nonneg (Real.sqrt_nonneg c) (norm_nonneg y)
  nlinarith [norm_nonneg (t.functional.gnsStarAlgHom x y)]

end Kadison.FreeCreation

namespace Kadison

open Filter _root_.Topology

lemma propagation_limit_bound (D R : ℝ) (a b : ℕ → ℝ)
    (hD : ∀ n, D≤R+a n) (ha : ∀ n, a n≤R+b n)
    (hb : Tendsto b atTop (𝓝 0)) : D≤2*R := by
  apply le_of_forall_pos_le_add
  intro η hη
  obtain ⟨n, hn⟩ := (hb.eventually_le_const hη).exists
  have h := (hD n).trans (add_le_add le_rfl ((ha n).trans (add_le_add le_rfl hn)))
  linarith

end Kadison

end

end
end

end OAI
