import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.TracialCohomology.MixedWords
import OAI.Analysis.TracialCohomology.PatchTraces

namespace OAI

/-! Patch bounds for bounded Hochschild cohomology. -/

noncomputable section

open scoped ComplexOrder
namespace PopaPatching
variable {C B G M : Type*} [Group G] [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

lemma rank_nonneg (τ : M →ₚ[ℂ] ℂ) (v : Rep G M) : 0≤Rep.rank τ v :=
  (Complex.nonneg_iff.mp (τ.map_nonneg v.support_projection.nonneg)).1
lemma rank_le_one (τ : M →ₚ[ℂ] ℂ) (h1 : τ 1=1) (v : Rep G M) : Rep.rank τ v≤1 := by
  have hh := Complex.re_le_re (τ.monotone v.support_projection.le_one)
  change (τ v.support).re ≤ (τ 1).re at hh
  simpa only [Rep.rank,h1,Complex.one_re] using hh

lemma good_short_bound (τ : M →ₚ[ℂ] ℂ) (h1 : τ 1=1)
    (a : C → M) (γ : B → G) (L : ℕ) (ε : ℕ → ℝ) (hε : ∀ n, 0≤ε n) (hmono : Monotone ε)
    (v : Rep G M) (hv : Good τ a γ L ε v) (l : List (Letter C B)) (k : ℕ)
    (hl : l.length≤L) (hk : l.length≤k) (hd : degree γ l ≠ 1) :
    ‖τ (evaluate a γ v l)‖≤ε k := by
  exact (hv l hl hd).trans ((mul_le_mul_of_nonneg_right (hmono hk) (rank_nonneg τ v)).trans
    (mul_le_of_le_one_right (hε k) (rank_le_one τ h1 v)))

lemma projection_trace_real (τ : M →ₚ[ℂ] ℂ) {p : M} (hp : IsStarProjection p) :
    τ p=((τ p).re:ℂ) := by
  exact Complex.ext rfl (Complex.nonneg_iff.mp (τ.map_nonneg hp.nonneg)).2.symm

lemma residual_scalar (τ : M →ₚ[ℂ] ℂ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (v : Rep G M) {p : M} (hp : IsStarProjection p) (hp0 : p ≠ 0) (hpv : p=1-v.support)
    (Y : M) :
    ((τ p).re:ℂ)*PopaCorner.trace hp τ (PopaCorner.compress hp Y)=τ Y-τ (v.support*Y) := by
  rw [←trace_rescale τ hfaith hp hp0]
  change τ (p*Y*p)=_
  rw [htr (p*Y) p,←mul_assoc,hp.isIdempotentElem.eq,hpv,sub_mul,one_mul,map_sub]

lemma residual_scalar_bound (τ : M →ₚ[ℂ] ℂ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (v : Rep G M)
    {p : M} (hp : IsStarProjection p) (hp0 : p ≠ 0) (hpv : p=1-v.support)
    (Y : M) (E δ : ℝ) (hδ : 0<δ) (hpδ : δ≤(τ p).re)
    (hY : ‖τ Y‖≤E) (hfY : ‖τ (v.support*Y)‖≤E) :
    ‖PopaCorner.trace hp τ (PopaCorner.compress hp Y)‖≤2*E/δ := by
  have ht : 0<(τ p).re := lt_of_lt_of_le hδ hpδ
  have hh := norm_sub_le (τ Y) (τ (v.support*Y))
  rw [←residual_scalar τ htr hfaith v hp hp0 hpv Y,norm_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht] at hh
  apply (le_div_iff₀ hδ).mpr
  nlinarith [norm_nonneg (PopaCorner.trace hp τ (PopaCorner.compress hp Y))]

lemma scalar_prod_bound {K : Type*} (l : List K) (c : K → ℂ)
    (hc : ∀ j ∈ l, ‖c j‖≤1) (j : K) (hj : j ∈ l) (E : ℝ) (hE : ‖c j‖≤E) :
    ‖(l.map c).prod‖≤E := by
  obtain ⟨s,t,rfl⟩ := List.mem_iff_append.mp hj
  have hs := prod_norm_le s c (fun i hi => hc i (by simp [hi]))
  have ht := prod_norm_le t c (fun i hi => hc i (by simp [hi]))
  simp only [List.map_append,List.prod_append,List.map_cons,List.prod_cons,norm_mul]
  calc
    _ ≤ 1*(‖c j‖*1) := mul_le_mul hs (mul_le_mul_of_nonneg_left ht (norm_nonneg _))
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by norm_num)
    _ ≤ E := by simpa using hE

lemma norm_list_sum_le (l : List ℂ) : ‖l.sum‖≤(l.map norm).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.sum_cons,List.map_cons]
    exact (norm_add_le _ _).trans (add_le_add le_rfl ih)

lemma patch_sum_bound {K : Type*} (l : List K) (z : ℂ) (b : K → ℂ) (c : K → ℝ)
    (E r Q H : ℝ) (_hE : 0≤E) (_hr : 0≤r) (hQ : 0≤Q) (_hH : 0≤H)
    (hc : ∀ i ∈ l, 0≤c i) (hc1 : (l.map c).sum≤1)
    (hz : ‖z‖≤E*r) (hb : ∀ i ∈ l, ‖b i+(c i:ℂ)*z‖≤H*Q)
    (hN : (l.length:ℝ)*H≤E) :
    ‖z+(l.map b).sum‖≤E*(r+Q) := by
  let s := (l.map c).sum
  have hs : 0 ≤ s := List.sum_nonneg (by simpa only [List.mem_map] using
    (show ∀ x ∈ l.map c,0≤x from by
      intro x hx; obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx; exact hc i hi))
  have hsum : ((l.map c).sum:ℂ)=(l.map (fun i => (c i:ℂ))).sum := by
    simpa only [List.map_map,Function.comp_def,Complex.ofRealHom_eq_coe] using map_list_sum (Complex.ofRealHom) (l.map c)
  have heq : z+(l.map b).sum=(1-(s:ℂ))*z+(l.map (fun i => b i+(c i:ℂ)*z)).sum := by
    rw [List.sum_map_add,List.sum_map_mul_right,←hsum]
    dsimp [s]
    ring
  rw [heq]
  calc
    _ ≤ ‖(1-(s:ℂ))*z‖+‖(l.map (fun i => b i+(c i:ℂ)*z)).sum‖ := norm_add_le _ _
    _ ≤ (1-s)*‖z‖+(l.length:ℝ)*(H*Q) := by
      apply add_le_add
      · rw [norm_mul,←Complex.ofReal_one,←Complex.ofReal_sub,Complex.norm_real,
          Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hc1)]
      · exact (norm_list_sum_le _).trans (by
          calc
            _ ≤ (l.map (fun _ => H*Q)).sum := by
              simpa only [List.map_map,Function.comp_def] using List.sum_le_sum hb
            _ = _ := by simp)
    _ ≤ E*r+E*Q := by
      have hcz := mul_le_of_le_one_left (norm_nonneg z) (show 1-s≤1 by linarith)
      have hq := mul_le_mul_of_nonneg_right hN hQ
      nlinarith
    _ = _ := by ring
end PopaPatching

open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity PopaPatching
universe u
variable {C B G : Type*} [Group G]
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

lemma preGNS_real_smul (r : ℝ) (a : M) : τ.toPreGNS (r • a)=r • τ.toPreGNS a := rfl

include h1 in
lemma good_short_bound (a : C → M) (γ : B → G) (L : ℕ) (ε : ℕ → ℝ)
    (hε : ∀ n, 0≤ε n) (hmono : Monotone ε) (v : Rep G M)
    (hv : Good e τ hτ htr hfaith a γ L ε v) (l : List (Letter C B)) (k : ℕ)
    (hl : l.length≤L) (hk : l.length≤k) (hd : degree γ l ≠ 1) :
    ‖τ.toPreGNS (average e τ hτ htr hfaith (evaluate a γ v l))‖≤ε k := by
  exact ((hv.2) l hl hd).trans ((mul_le_mul_of_nonneg_right (hmono hk) (rank_nonneg τ v)).trans
    (mul_le_of_le_one_right (hε k) (rank_le_one τ h1 v)))

include h1 in
lemma residual_coefficient (v : Rep G M) {p : M} (hp : IsStarProjection p) (hp0 : p ≠ 0)
    (hpv : p=1-v.support) (Y : M) :
    (τ p).re • cornerCoefficient e τ hτ htr hfaith hp Y =
      average e τ hτ htr hfaith Y-average e τ hτ htr hfaith (v.support*Y) := by
  have ht := HochschildDiffuse.projection_trace_pos τ hfaith hp hp0
  rw [cornerCoefficient,smul_smul,mul_inv_cancel₀ ht.ne',one_smul,
    average_trace e τ hτ htr hfaith h1 (p*Y) p,←mul_assoc,hp.isIdempotentElem.eq,
    hpv,sub_mul,one_mul]
  exact map_sub (expectation e τ hτ htr hfaith h1) _ _

include h1 in
lemma residual_coefficient_bound (v : Rep G M) {p : M} (hp : IsStarProjection p)
    (hp0 : p ≠ 0) (hpv : p=1-v.support) (Y : M) (E δ : ℝ) (hδ : 0<δ)
    (hpδ : δ≤(τ p).re) (hY : ‖τ.toPreGNS (average e τ hτ htr hfaith Y)‖≤E)
    (hfY : ‖τ.toPreGNS (average e τ hτ htr hfaith (v.support*Y))‖≤E) :
    ‖τ.toPreGNS (cornerCoefficient e τ hτ htr hfaith hp Y)‖≤2*E/δ := by
  have ht : 0<(τ p).re := lt_of_lt_of_le hδ hpδ
  have hh := norm_sub_le (τ.toPreGNS (average e τ hτ htr hfaith Y))
    (τ.toPreGNS (average e τ hτ htr hfaith (v.support*Y)))
  rw [←map_sub,←residual_coefficient e τ hτ htr hfaith h1 v hp hp0 hpv Y,
    preGNS_real_smul τ,norm_smul,Real.norm_eq_abs,abs_of_pos ht] at hh
  apply (le_div_iff₀ hδ).mpr
  nlinarith [norm_nonneg (τ.toPreGNS (cornerCoefficient e τ hτ htr hfaith hp Y))]

include htr in
lemma product_l2_bound {K : Type*} (l : List K) (c : K → M)
    (hc : ∀ j ∈ l, ‖c j‖≤1) (j : K) (hj : j ∈ l) (E : ℝ)
    (hE : ‖τ.toPreGNS (c j)‖≤E) : ‖τ.toPreGNS ((l.map c).prod)‖≤E := by
  obtain ⟨s,t,rfl⟩ := List.mem_iff_append.mp hj
  have hs := prod_norm_le s c (fun i hi => hc i (by simp [hi]))
  have ht := prod_norm_le t c (fun i hi => hc i (by simp [hi]))
  simp only [List.map_append,List.prod_append,List.map_cons,List.prod_cons]
  exact (preGNS_norm_mul_le τ _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) hs).trans
    ((preGNS_norm_mul_right_le τ htr _ _).trans
      ((mul_le_of_le_one_left (norm_nonneg _) ht).trans hE)))

lemma norm_list_sum {V : Type*} [SeminormedAddCommGroup V] (l : List V) :
    ‖l.sum‖≤(l.map norm).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.sum_cons,List.map_cons]
    exact (norm_add_le _ _).trans (add_le_add le_rfl ih)

lemma patch_sum_bound {V K : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    (l : List K) (z : V) (b : K → V) (c : K → ℝ)
    (E r Q H : ℝ) (_hE : 0≤E) (_hr : 0≤r) (hQ : 0≤Q) (_hH : 0≤H)
    (hc : ∀ i ∈ l, 0≤c i) (hc1 : (l.map c).sum≤1)
    (hz : ‖z‖≤E*r) (hb : ∀ i ∈ l, ‖b i+c i • z‖≤H*Q)
    (hN : (l.length:ℝ)*H≤E) : ‖z+(l.map b).sum‖≤E*(r+Q) := by
  let s := (l.map c).sum
  have hsum : (l.map (fun i => c i • z)).sum=s • z := by
    simpa only [List.map_map,Function.comp_def,s] using (List.sum_smul (l:=l.map c) (x:=z)).symm
  have heq : z+(l.map b).sum=(1-s) • z+(l.map (fun i => b i+c i • z)).sum := by
    rw [List.sum_map_add,hsum]
    change _=(1-s) • z+((l.map b).sum+s • z)
    rw [sub_smul,one_smul]
    abel
  rw [heq]
  calc
    _ ≤ ‖(1-s) • z‖+‖(l.map (fun i => b i+c i • z)).sum‖ := norm_add_le _ _
    _ ≤ (1-s)*‖z‖+(l.length:ℝ)*(H*Q) := by
      apply add_le_add
      · rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hc1)]
      · exact (norm_list_sum _).trans (by
          calc
            _ ≤ (l.map (fun _ => H*Q)).sum := by
              simpa only [List.map_map,Function.comp_def] using List.sum_le_sum hb
            _ = _ := by simp)
    _ ≤ E*r+E*Q := by
      have hs : 0 ≤ s := List.sum_nonneg (by
        intro x hx; obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx; exact hc i hi)
      have hcz := mul_le_of_le_one_left (norm_nonneg z) (show 1-s≤1 by linarith)
      have hq := mul_le_mul_of_nonneg_right hN hQ
      nlinarith
    _ = _ := by ring
end PopaCenter

end

end OAI
