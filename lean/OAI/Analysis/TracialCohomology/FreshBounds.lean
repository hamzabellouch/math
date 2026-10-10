import Mathlib
import OAI.Analysis.BoundedHochschild.CocycleNormalParts
import OAI.Analysis.BoundedHochschild.FactorFinitePaths
import OAI.Analysis.BoundedHochschild.FreeWords
import OAI.Analysis.BoundedHochschild.MatrixDisplacement
import OAI.Analysis.BoundedHochschild.UnitaryLifts
import OAI.Analysis.TracialCohomology.MarkedWords
import OAI.Analysis.TracialCohomology.PatchBounds

namespace OAI

/-! Fresh bounds for bounded Hochschild cohomology. -/

noncomputable section

open scoped ComplexOrder
namespace PopaPatching
attribute [local instance] Classical.propDecidable
variable {C B G M : Type*} [Group G] [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]

def identitySingleton (γ : B → G) (bs : List B) : Prop := ∃ b, bs=[b] ∧ γ b=1

lemma norm_trace_projection (τ : M →ₚ[ℂ] ℂ) {q : M} (hq : IsStarProjection q) :
    ‖τ q‖=(τ q).re := by
  rw [projection_trace_real τ hq,Complex.norm_real,Real.norm_eq_abs]
  exact abs_of_nonneg (Complex.nonneg_iff.mp (τ.map_nonneg hq.nonneg)).1

lemma norm_le_error (z t : ℂ) : ‖z‖≤‖z-t‖+‖t‖ := by
  simpa only [sub_add_cancel] using norm_add_le (z-t) t

lemma singleton_cancellation_bound (τ : M →ₚ[ℂ] ℂ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0)
    (v : Rep G M) {p q : M} (hp : IsStarProjection p) (hp0 : p ≠ 0) (hpv : p=1-v.support)
    (hq : IsStarProjection q) (Y : M) (z : ℂ) (E δ θ : ℝ)
    (hE : 0≤E) (hδ : 0<δ) (hpδ : δ≤(τ p).re) (hY : ‖τ Y‖≤E)
    (hz : ‖z-PopaCorner.trace hp τ (PopaCorner.compress hp Y)*τ q‖≤θ*(τ q).re) :
    ‖z+(((τ q).re/(τ p).re:ℝ):ℂ)*τ (v.support*Y)‖≤(E/δ+θ)*(τ q).re := by
  let c := PopaCorner.trace hp τ (PopaCorner.compress hp Y)
  let A : ℝ := (τ q).re/(τ p).re
  have ht : 0<(τ p).re := lt_of_lt_of_le hδ hpδ
  have hqnonneg : 0≤(τ q).re := (Complex.nonneg_iff.mp (τ.map_nonneg hq.nonneg)).1
  have hA : 0≤A := div_nonneg hqnonneg ht.le
  have hc := residual_scalar τ htr hfaith v hp hp0 hpv Y
  have hc' : c*τ q+(A:ℂ)*τ (v.support*Y)=(A:ℂ)*τ Y := by
    rw [projection_trace_real τ hq]
    have he : (A:ℂ)*((τ p).re:ℂ)=((τ q).re:ℂ) := by
      rw [←Complex.ofReal_mul]
      congr 1
      exact div_mul_cancel₀ _ ht.ne'
    calc
      _ = (A:ℂ)*(((τ p).re:ℂ)*c+τ (v.support*Y)) := by rw [mul_add,←mul_assoc,he]; ring
      _ = _ := by rw [hc,sub_add_cancel]
  have he : z+(A:ℂ)*τ (v.support*Y)=(z-c*τ q)+(A:ℂ)*τ Y := by rw [←hc']; ring
  change ‖z+(A:ℂ)*τ (v.support*Y)‖≤_
  rw [he]
  calc
    _ ≤ ‖z-c*τ q‖+‖(A:ℂ)*τ Y‖ := norm_add_le _ _
    _ ≤ θ*(τ q).re+A*E := by
      apply add_le_add hz
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hA]
      exact mul_le_mul_of_nonneg_left hY hA
    _ ≤ (E/δ+θ)*(τ q).re := by
      have hdiv : E/(τ p).re≤E/δ := div_le_div_of_nonneg_left hE hδ hpδ
      have hh := mul_le_mul_of_nonneg_left hdiv hqnonneg
      dsimp [A]
      simp only [div_eq_mul_inv] at hh ⊢
      nlinarith

theorem many_blocks_bound (τ : M →ₚ[ℂ] ℂ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)
    (a : C → M) (ha : ∀ c, ‖a c‖≤1) (γ : B → G) (b0 : B) (hb0 : γ b0=1)
    (L : ℕ) (ε : ℕ → ℝ) (hε : ∀ n, 0≤ε n) (hmono : Monotone ε)
    (v : Rep G M) (hv : Good τ a γ L ε v)
    {p q : M} (hp : IsStarProjection p) (hp0 : p ≠ 0) (hpv : p=1-v.support)
    (hq : IsStarProjection q) (hq0 : q ≠ 0) (w : Rep G M) (hw : w.support=q)
    (δ θ : ℝ) (hδ : 0<δ) (hpδ : δ≤(τ p).re) (hθ : 0≤θ)
    (hkill : ∀ bs : List B, bs.length≤L → (bs.map γ).prod ≠ 1 → τ (w ((bs.map γ).prod))=0)
    (he : ∀ l : List (Letter C B), l.length≤L →
      ‖(PopaCorner.trace hq τ).toPreGNS (PopaCorner.compress hq (evaluate a γ v l)-
        (PopaCorner.trace hp τ (PopaCorner.compress hp (evaluate a γ v l))) • 1)‖≤θ)
    (b : List (Block C B)) (hb : 2≤b.length) (hL : (eraseBlocks b).length≤L)
    (hd : degree γ (eraseBlocks b) ≠ 1) :
    ‖τ ((b.map (fun j => w (γ j.1)*evaluate a γ v j.2)).prod)‖≤
      (2*ε ((eraseBlocks b).length-1)/δ+(L:ℝ)*θ)*(τ q).re := by
  let k := (eraseBlocks b).length
  let E := ε (k-1)
  let c : Block C B → ℂ := fun j => PopaCorner.trace hp τ (PopaCorner.compress hp (evaluate a γ v j.2))
  have hseg (j : Block C B) (hj : j ∈ b) : j.2.length+1≤k-1 := by
    have hh := segment_length_bound b j hj
    dsimp [k]; omega
  have hc (j : Block C B) (hj : j ∈ b) : ‖c j‖≤1 :=
    corner_scalar_norm_le τ hfaith hp hp0 _ (evaluate_norm_le a ha γ v _)
  have hbe := block_trace_error τ htr hfaith w hq hq0 hw b (fun j => γ j.1)
    (fun j => evaluate a γ v j.2) c (by intro hh; simp [hh] at hb)
    (fun j _ => evaluate_norm_le a ha γ v _) hc θ
    (fun j hj => he j.2 (by have hh := hseg j hj; dsimp [k] at hh; omega))
  have ht : 0<(τ q).re := HochschildDiffuse.projection_trace_pos τ hfaith hq hq0
  have hbl : (b.length:ℝ)≤L := by exact_mod_cast (blocks_length_le b).trans hL
  by_cases hg : (b.map (fun j => γ j.1)).prod=1
  · obtain ⟨j,hj,hjd⟩ := exists_nontrivial_segment γ b hd hg
    have hjlen := hseg j hj
    have hY : ‖τ (evaluate a γ v j.2)‖≤E := good_short_bound τ h1 a γ L ε hε hmono v hv j.2
      (k-1) (by dsimp [k] at hjlen; omega) (by omega) hjd
    have hfY : ‖τ (v.support*evaluate a γ v j.2)‖≤E := by
      have hh := good_short_bound τ h1 a γ L ε hε hmono v hv (Sum.inr b0::j.2)
        (k-1) (by simp only [List.length_cons]; dsimp [k] at hjlen; omega)
        (by simp only [List.length_cons]; omega) (by simpa [degree_cons,letterDegree,hb0] using hjd)
      simpa only [evaluate_cons,letterValue,Sum.elim_inr,hb0,Rep.support] using hh
    have hcj : ‖c j‖≤2*E/δ := residual_scalar_bound τ htr hfaith v hp hp0 hpv
      (evaluate a γ v j.2) E δ hδ hpδ hY hfY
    have hcp := scalar_prod_bound b c hc j hj (2*E/δ) hcj
    rw [hg,show w 1=q from hw,mul_comm (b.map c).prod] at hbe
    have hn := norm_le_error (τ ((b.map (fun j => w (γ j.1)*evaluate a γ v j.2)).prod))
      (τ q*(b.map c).prod)
    rw [norm_mul,norm_trace_projection τ hq] at hn
    have hh := mul_le_mul_of_nonneg_left hcp ht.le
    have hθb := mul_le_mul_of_nonneg_right hbl hθ
    change _ ≤ (2*E/δ+(L:ℝ)*θ)*(τ q).re
    nlinarith
  · have hk : τ (w ((b.map (fun j => γ j.1)).prod))=0 := by
      have hh := hkill (b.map Prod.fst) (by simpa using (blocks_length_le b).trans hL)
        (by simpa only [List.map_map,Function.comp_def] using hg)
      simpa only [List.map_map,Function.comp_def] using hh
    rw [hk,mul_zero,sub_zero] at hbe
    have hEn : 0≤2*E/δ := div_nonneg (mul_nonneg (by norm_num) (hε _)) hδ.le
    have hθb := mul_le_mul_of_nonneg_right hbl hθ
    change _ ≤ (2*E/δ+(L:ℝ)*θ)*(τ q).re
    nlinarith

@[simp] lemma identitySingleton_one (γ : B → G) (b : B) : identitySingleton γ [b] ↔ γ b=1 := by
  simp [identitySingleton]
@[simp] lemma identitySingleton_two (γ : B → G) (b c : B) (bs : List B) :
    ¬identitySingleton γ (b::c::bs) := by simp [identitySingleton]

theorem all_blocks_bound (τ : M →ₚ[ℂ] ℂ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
    (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)
    (a : C → M) (ha : ∀ c, ‖a c‖≤1) (γ : B → G) (b0 : B) (hb0 : γ b0=1)
    (L : ℕ) (ε : ℕ → ℝ) (hε : ∀ n, 0≤ε n) (hmono : Monotone ε)
    (v : Rep G M) (hv : Good τ a γ L ε v)
    {p q : M} (hp : IsStarProjection p) (hp0 : p ≠ 0) (hpv : p=1-v.support)
    (hq : IsStarProjection q) (hq0 : q ≠ 0) (w : Rep G M) (hw : w.support=q)
    (δ θ : ℝ) (hδ : 0<δ) (hpδ : δ≤(τ p).re) (hθ : 0≤θ)
    (hkill : ∀ bs : List B, bs.length≤L → (bs.map γ).prod ≠ 1 → τ (w ((bs.map γ).prod))=0)
    (he : ∀ l : List (Letter C B), l.length≤L →
      ‖(PopaCorner.trace hq τ).toPreGNS (PopaCorner.compress hq (evaluate a γ v l)-
        (PopaCorner.trace hp τ (PopaCorner.compress hp (evaluate a γ v l))) • 1)‖≤θ)
    (b : List (Block C B)) (hb : b ≠ []) (hL : (eraseBlocks b).length≤L)
    (hd : degree γ (eraseBlocks b) ≠ 1) :
    ‖τ ((b.map (fun j => w (γ j.1)*evaluate a γ v j.2)).prod)+
      ((if identitySingleton γ (b.map Prod.fst) then (τ q).re/(τ p).re else 0 : ℝ):ℂ)*
        τ (evaluate a γ v (eraseBlocks b))‖≤
      (2*ε ((eraseBlocks b).length-1)/δ+(L:ℝ)*θ)*(τ q).re := by
  classical
  cases b with
  | nil => exact False.elim (hb rfl)
  | cons j bs =>
    cases bs with
    | cons j' bs =>
      simp only [List.map_cons,identitySingleton_two,reduceIte,Complex.ofReal_zero,zero_mul,add_zero]
      exact many_blocks_bound τ htr hfaith h1 a ha γ b0 hb0 L ε hε hmono v hv
        hp hp0 hpv hq hq0 w hw δ θ hδ hpδ hθ hkill he (j::j'::bs) (by simp) hL hd
    | nil =>
      have hlen : (eraseBlocks [j]).length=j.2.length+1 := by simp [eraseBlocks]
      have hjL : j.2.length≤L := by rw [hlen] at hL; omega
      have hL1 : (1:ℝ)≤L := by exact_mod_cast (show 1≤L by rw [hlen] at hL; omega)
      have ht : 0<(τ q).re := HochschildDiffuse.projection_trace_pos τ hfaith hq hq0
      let c := PopaCorner.trace hp τ (PopaCorner.compress hp (evaluate a γ v j.2))
      have hbe := block_trace_error τ htr hfaith w hq hq0 hw [j] (fun j => γ j.1)
        (fun j => evaluate a γ v j.2) (fun j => PopaCorner.trace hp τ (PopaCorner.compress hp (evaluate a γ v j.2)))
        (by simp) (fun j _ => evaluate_norm_le a ha γ v _)
        (fun j _ => corner_scalar_norm_le τ hfaith hp hp0 _ (evaluate_norm_le a ha γ v _)) θ
        (fun k hk => by
          have hk' : k=j := by simpa using hk
          subst k
          exact he j.2 hjL)
      simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,
        List.length_cons,List.length_nil,Nat.zero_add,Nat.cast_one,one_mul] at hbe
      have hEn := hε j.2.length
      have hEdiv : 0≤ε j.2.length/δ := div_nonneg hEn hδ.le
      simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,
        identitySingleton_one,hlen,Nat.add_sub_cancel]
      by_cases hg : γ j.1=1
      · rw [ite_eq_left hg]
        have hYd : degree γ j.2 ≠ 1 := by
          simpa [eraseBlocks,degree_cons,letterDegree,hg] using hd
        have hY := good_short_bound τ h1 a γ L ε hε hmono v hv j.2 j.2.length hjL le_rfl hYd
        have hold : evaluate a γ v (eraseBlocks [j])=v.support*evaluate a γ v j.2 := by
          rw [evaluate_blocks]
          simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,hg,Rep.support]
        have hbe' : ‖τ (w (γ j.1)*evaluate a γ v j.2)-c*τ q‖≤θ*(τ q).re := by
          simpa only [hg,show w 1=q from hw] using hbe
        have hh := singleton_cancellation_bound τ htr hfaith v hp hp0 hpv hq
          (evaluate a γ v j.2) (τ (w (γ j.1)*evaluate a γ v j.2))
          (ε j.2.length) δ θ hEn hδ hpδ hY hbe'
        rw [hold]
        have hθL := mul_le_mul_of_nonneg_right hL1 hθ
        have heq : 2*ε j.2.length/δ=2*(ε j.2.length/δ) := by ring
        rw [heq]
        nlinarith
      · rw [ite_eq_right hg,Complex.ofReal_zero,zero_mul,add_zero]
        have hk := hkill [j.1] (by simp only [List.length_cons,List.length_nil]; rw [hlen] at hL; omega)
          (by simpa using hg)
        simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one] at hk
        rw [hk,mul_zero,sub_zero] at hbe
        have hθL := mul_le_mul_of_nonneg_right hL1 hθ
        have heq : 2*ε j.2.length/δ=2*(ε j.2.length/δ) := by ring
        rw [heq]
        nlinarith

end PopaPatching

open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity PopaPatching
universe u
variable {G : Type*} [Group G]
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

include h1 in
lemma singleton_cancellation_bound (v : Rep G M) {p q : M} (hp : IsStarProjection p)
    (hp0 : p ≠ 0) (hpv : p=1-v.support) (hq : IsStarProjection q)
    (hEq : average e τ hτ htr hfaith q=(τ q).re • (1:M)) (Y z : M) (E δ θ : ℝ)
    (hE : 0≤E) (hδ : 0<δ) (hpδ : δ≤(τ p).re)
    (hY : ‖τ.toPreGNS (average e τ hτ htr hfaith Y)‖≤E)
    (hz : ‖τ.toPreGNS (z-cornerCoefficient e τ hτ htr hfaith hp Y*average e τ hτ htr hfaith q)‖≤θ*(τ q).re) :
    ‖τ.toPreGNS (z+((τ q).re/(τ p).re) • average e τ hτ htr hfaith (v.support*Y))‖≤(E/δ+θ)*(τ q).re := by
  let c := cornerCoefficient e τ hτ htr hfaith hp Y
  let A : ℝ := (τ q).re/(τ p).re
  have ht : 0<(τ p).re := lt_of_lt_of_le hδ hpδ
  have hqnonneg : 0≤(τ q).re := (Complex.nonneg_iff.mp (τ.map_nonneg hq.nonneg)).1
  have hA : 0≤A := div_nonneg hqnonneg ht.le
  have hc := residual_coefficient e τ hτ htr hfaith h1 v hp hp0 hpv Y
  have hc' : c*average e τ hτ htr hfaith q+A • average e τ hτ htr hfaith (v.support*Y)=
      A • average e τ hτ htr hfaith Y := by
    rw [hEq,mul_smul_comm,mul_one]
    have he : A*(τ p).re=(τ q).re := div_mul_cancel₀ _ ht.ne'
    calc
      _ = A • ((τ p).re • c+average e τ hτ htr hfaith (v.support*Y)) := by
        rw [smul_add,smul_smul,he]
      _ = _ := by rw [hc,sub_add_cancel]
  have he : z+A • average e τ hτ htr hfaith (v.support*Y)=
      (z-c*average e τ hτ htr hfaith q)+A • average e τ hτ htr hfaith Y := by rw [←hc']; abel
  change ‖τ.toPreGNS (z+A • average e τ hτ htr hfaith (v.support*Y))‖≤_
  rw [he,map_add]
  calc
    _ ≤ ‖τ.toPreGNS (z-c*average e τ hτ htr hfaith q)‖+
        ‖τ.toPreGNS (A • average e τ hτ htr hfaith Y)‖ := norm_add_le _ _
    _ ≤ θ*(τ q).re+A*E := by
      apply add_le_add hz
      rw [preGNS_real_smul τ,norm_smul,Real.norm_eq_abs,abs_of_nonneg hA]
      exact mul_le_mul_of_nonneg_left hY hA
    _ ≤ (E/δ+θ)*(τ q).re := by
      have hdiv : E/(τ p).re≤E/δ := div_le_div_of_nonneg_left hE hδ hpδ
      have hh := mul_le_mul_of_nonneg_left hdiv hqnonneg
      dsimp [A]
      simp only [div_eq_mul_inv] at hh ⊢
      nlinarith
end PopaCenter

namespace PopaCenter
open PopaPatching
variable {C B G M : Type*} [Group G] [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
omit [PartialOrder M] [StarOrderedRing M] in
lemma cyclic_blocks {N : Type*} (T : M → N) (hT : ∀ x y : M, T (x*y)=T (y*x))
    (a : C → M) (γ : B → G) (v w : Rep G M) (m : List (Mark C B))
    (hm : freshs m ≠ []) (hd : degree γ (m.map eraseMark) ≠ 1) :
    ∃ b : List (Block C B), b ≠ [] ∧ b.map Prod.fst=freshs m ∧
      (eraseBlocks b).length=m.length ∧ degree γ (eraseBlocks b) ≠ 1 ∧
      T (markedEval a γ v w m)=T ((b.map (fun j => w (γ j.1)*evaluate a γ v j.2)).prod) ∧
      T (evaluate a γ v (m.map eraseMark))=T (evaluate a γ v (eraseBlocks b)) := by
  let pre := (splitMarked m).1
  let bs := (splitMarked m).2
  have hbs : bs ≠ [] := freshs_nonempty_split m hm
  let b := appendTail bs pre
  have he : flattenBlocks b=flattenBlocks bs++pre.map oldMark := appendTail_spec bs pre hbs
  have hm' : m=pre.map oldMark++flattenBlocks bs := splitMarked_spec m
  have her : m.map eraseMark=pre++eraseBlocks bs := by rw [hm']; simp only [List.map_append,erase_old_list,erase_flatten]
  have he' : eraseBlocks b=eraseBlocks bs++pre := by
    rw [←erase_flatten,he,List.map_append,erase_flatten,erase_old_list]
  have hf : b.map Prod.fst=freshs m := by
    rw [←freshs_flatten,he,hm']
    simp
  have hlen : (eraseBlocks b).length=m.length := by
    rw [he',List.length_append,hm',List.length_append,List.length_map]
    have hh := congrArg List.length (erase_flatten bs)
    simp only [List.length_map] at hh
    omega
  refine ⟨b,fun hh => hm (by rw [←hf,hh,List.map_nil]),hf,hlen,?_,?_,?_⟩
  · rw [he']
    exact degree_rotation_ne_one γ pre (eraseBlocks bs) (by rwa [her] at hd)
  · rw [←markedEval_flatten,he,hm',markedEval_append,markedEval_append]
    exact hT _ _
  · rw [her,he',evaluate_append,evaluate_append]
    exact hT _ _
end PopaCenter

open scoped ComplexOrder
namespace PopaCenter
open BoundedHochschild HochschildRigidity PopaPatching
attribute [local instance] Classical.propDecidable
universe u
variable {C B G : Type*} [Group G]
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
variable (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (τ : M →ₚ[ℂ] ℂ)
  (hτ : TraceInPredual e τ) (htr : ∀ a b : M, τ (a*b)=τ (b*a))
  (hfaith : ∀ a : M, τ (star a*a)=0 → a=0) (h1 : τ 1=1)

include h1 in
theorem many_blocks_bound (hII : PopaTypeII.NoAbelianCorners M)
    (a : C → M) (ha : ∀ c, ‖a c‖≤1) (γ : B → G) (b0 : B) (hb0 : γ b0=1)
    (L : ℕ) (ε : ℕ → ℝ) (hε : ∀ n, 0≤ε n) (hmono : Monotone ε)
    (v : Rep G M) (hv : Good e τ hτ htr hfaith a γ L ε v)
    {p q : M} (hp : IsStarProjection p) (hp0 : p ≠ 0) (hpv : p=1-v.support)
    (hEp : Homogeneous e τ hτ htr hfaith p)
    (hq : IsStarProjection q) (hq0 : q ≠ 0) (hEq : Homogeneous e τ hτ htr hfaith q)
    (w : Rep G M) (hw : w.support=q)
    (δ θ : ℝ) (hδ : 0<δ) (hpδ : δ≤(τ p).re) (hθ : 0≤θ)
    (hkill : ∀ bs : List B, bs.length≤L → (bs.map γ).prod ≠ 1 → average e τ hτ htr hfaith (w ((bs.map γ).prod))=0)
    (he : ∀ l : List (Letter C B), l.length≤L →
      ‖(PopaCorner.trace hq τ).toPreGNS (PopaCorner.compress hq (evaluate a γ v l)-
        PopaCorner.compress hq (cornerCoefficient e τ hτ htr hfaith hp (evaluate a γ v l)))‖≤θ)
    (b : List (Block C B)) (hb : 2≤b.length) (hL : (eraseBlocks b).length≤L)
    (hd : degree γ (eraseBlocks b) ≠ 1) :
    ‖τ.toPreGNS (average e τ hτ htr hfaith ((b.map (fun j => w (γ j.1)*evaluate a γ v j.2)).prod))‖≤
      (2*ε ((eraseBlocks b).length-1)/δ+(L:ℝ)*θ)*(τ q).re := by
  let k := (eraseBlocks b).length
  let E := ε (k-1)
  let c : Block C B → M := fun j => cornerCoefficient e τ hτ htr hfaith hp (evaluate a γ v j.2)
  have hseg (j : Block C B) (hj : j ∈ b) : j.2.length+1≤k-1 := by
    have hh := segment_length_bound b j hj
    dsimp [k]; omega
  have hc (j : Block C B) (hj : j ∈ b) : ‖c j‖≤1 :=
    (cornerCoefficient_spec e τ hτ htr hfaith h1 hII hp hp0 hEp _).2.trans (evaluate_norm_le a ha γ v _)
  have hcZ (j : Block C B) : Central (c j) := cornerCoefficient_central e τ hτ htr hfaith hp _
  have hbe := block_average_error e τ hτ htr hfaith h1 w hq hq0 hw hEq b (fun j => γ j.1)
    (fun j => evaluate a γ v j.2) c hcZ (by intro hh; simp [hh] at hb)
    (fun j _ => evaluate_norm_le a ha γ v _) hc θ hθ
    (fun j hj => he j.2 (by have hh := hseg j hj; dsimp [k] at hh; omega))
  have ht : 0<(τ q).re := HochschildDiffuse.projection_trace_pos τ hfaith hq hq0
  have hbl : (b.length:ℝ)≤L := by exact_mod_cast (blocks_length_le b).trans hL
  by_cases hg : (b.map (fun j => γ j.1)).prod=1
  · obtain ⟨j,hj,hjd⟩ := exists_nontrivial_segment γ b hd hg
    have hjlen := hseg j hj
    have hY : ‖τ.toPreGNS (average e τ hτ htr hfaith (evaluate a γ v j.2))‖≤E :=
      good_short_bound e τ hτ htr hfaith h1 a γ L ε hε hmono v hv j.2
        (k-1) (by dsimp [k] at hjlen; omega) (by omega) hjd
    have hfY : ‖τ.toPreGNS (average e τ hτ htr hfaith (v.support*evaluate a γ v j.2))‖≤E := by
      have hh := good_short_bound e τ hτ htr hfaith h1 a γ L ε hε hmono v hv (Sum.inr b0::j.2)
        (k-1) (by simp only [List.length_cons]; dsimp [k] at hjlen; omega)
        (by simp only [List.length_cons]; omega) (by simpa [degree_cons,letterDegree,hb0] using hjd)
      simpa only [evaluate_cons,letterValue,Sum.elim_inr,hb0,Rep.support] using hh
    have hcj : ‖τ.toPreGNS (c j)‖≤2*E/δ := residual_coefficient_bound e τ hτ htr hfaith h1 v hp hp0 hpv
      (evaluate a γ v j.2) E δ hδ hpδ hY hfY
    have hcp := product_l2_bound τ htr b c hc j hj (2*E/δ) hcj
    rw [hg,show w 1=q from hw,hEq,mul_smul_comm,mul_one] at hbe
    have hn := norm_add_le
      (τ.toPreGNS (average e τ hτ htr hfaith ((b.map (fun j => w (γ j.1)*evaluate a γ v j.2)).prod)-
        (τ q).re • (b.map c).prod)) (τ.toPreGNS ((τ q).re • (b.map c).prod))
    rw [←map_add,sub_add_cancel,preGNS_real_smul τ,norm_smul,Real.norm_eq_abs,abs_of_pos ht] at hn
    have hh := mul_le_mul_of_nonneg_left hcp ht.le
    have hθb := mul_le_mul_of_nonneg_right hbl hθ
    change _ ≤ (2*E/δ+(L:ℝ)*θ)*(τ q).re
    nlinarith
  · have hk : average e τ hτ htr hfaith (w ((b.map (fun j => γ j.1)).prod))=0 := by
      have hh := hkill (b.map Prod.fst) (by simpa using (blocks_length_le b).trans hL)
        (by simpa only [List.map_map,Function.comp_def] using hg)
      simpa only [List.map_map,Function.comp_def] using hh
    rw [hk,mul_zero,sub_zero] at hbe
    have hEn : 0≤2*E/δ := div_nonneg (mul_nonneg (by norm_num) (hε _)) hδ.le
    have hθb := mul_le_mul_of_nonneg_right hbl hθ
    change _ ≤ (2*E/δ+(L:ℝ)*θ)*(τ q).re
    nlinarith

include h1 in
theorem all_blocks_bound (hII : PopaTypeII.NoAbelianCorners M)
    (a : C → M) (ha : ∀ c, ‖a c‖≤1) (γ : B → G) (b0 : B) (hb0 : γ b0=1)
    (L : ℕ) (ε : ℕ → ℝ) (hε : ∀ n, 0≤ε n) (hmono : Monotone ε)
    (v : Rep G M) (hv : Good e τ hτ htr hfaith a γ L ε v)
    {p q : M} (hp : IsStarProjection p) (hp0 : p ≠ 0) (hpv : p=1-v.support)
    (hEp : Homogeneous e τ hτ htr hfaith p)
    (hq : IsStarProjection q) (hq0 : q ≠ 0) (hEq : Homogeneous e τ hτ htr hfaith q)
    (w : Rep G M) (hw : w.support=q)
    (δ θ : ℝ) (hδ : 0<δ) (hpδ : δ≤(τ p).re) (hθ : 0≤θ)
    (hkill : ∀ bs : List B, bs.length≤L → (bs.map γ).prod ≠ 1 → average e τ hτ htr hfaith (w ((bs.map γ).prod))=0)
    (he : ∀ l : List (Letter C B), l.length≤L →
      ‖(PopaCorner.trace hq τ).toPreGNS (PopaCorner.compress hq (evaluate a γ v l)-
        PopaCorner.compress hq (cornerCoefficient e τ hτ htr hfaith hp (evaluate a γ v l)))‖≤θ)
    (b : List (Block C B)) (hb : b ≠ []) (hL : (eraseBlocks b).length≤L)
    (hd : degree γ (eraseBlocks b) ≠ 1) :
    ‖τ.toPreGNS (average e τ hτ htr hfaith ((b.map (fun j => w (γ j.1)*evaluate a γ v j.2)).prod)+
      (if identitySingleton γ (b.map Prod.fst) then (τ q).re/(τ p).re else 0 : ℝ) •
        average e τ hτ htr hfaith (evaluate a γ v (eraseBlocks b)))‖≤
      (2*ε ((eraseBlocks b).length-1)/δ+(L:ℝ)*θ)*(τ q).re := by
  classical
  cases b with
  | nil => exact False.elim (hb rfl)
  | cons j bs =>
    cases bs with
    | cons j' bs =>
      simp only [List.map_cons,identitySingleton_two,reduceIte,zero_smul,add_zero]
      exact many_blocks_bound e τ hτ htr hfaith h1 hII a ha γ b0 hb0 L ε hε hmono v hv
        hp hp0 hpv hEp hq hq0 hEq w hw δ θ hδ hpδ hθ hkill he (j::j'::bs) (by simp) hL hd
    | nil =>
      have hlen : (eraseBlocks [j]).length=j.2.length+1 := by simp [eraseBlocks]
      have hjL : j.2.length≤L := by rw [hlen] at hL; omega
      have hL1 : (1:ℝ)≤L := by exact_mod_cast (show 1≤L by rw [hlen] at hL; omega)
      have ht : 0<(τ q).re := HochschildDiffuse.projection_trace_pos τ hfaith hq hq0
      let c := cornerCoefficient e τ hτ htr hfaith hp (evaluate a γ v j.2)
      have hbe := block_average_error e τ hτ htr hfaith h1 w hq hq0 hw hEq [j] (fun j => γ j.1)
        (fun j => evaluate a γ v j.2) (fun j => cornerCoefficient e τ hτ htr hfaith hp (evaluate a γ v j.2))
        (fun j => cornerCoefficient_central e τ hτ htr hfaith hp _) (by simp)
        (fun j _ => evaluate_norm_le a ha γ v _)
        (fun j _ => (cornerCoefficient_spec e τ hτ htr hfaith h1 hII hp hp0 hEp _).2.trans
          (evaluate_norm_le a ha γ v _)) θ hθ
        (fun k hk => by
          have hk' : k=j := by simpa using hk
          subst k
          exact he j.2 hjL)
      simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,
        List.length_cons,List.length_nil,Nat.zero_add,Nat.cast_one,one_mul] at hbe
      have hEn := hε j.2.length
      have hEdiv : 0≤ε j.2.length/δ := div_nonneg hEn hδ.le
      simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,
        identitySingleton_one,hlen,Nat.add_sub_cancel]
      by_cases hg : γ j.1=1
      · rw [ite_eq_left hg]
        have hYd : degree γ j.2 ≠ 1 := by
          simpa [eraseBlocks,degree_cons,letterDegree,hg] using hd
        have hY := good_short_bound e τ hτ htr hfaith h1 a γ L ε hε hmono v hv j.2 j.2.length hjL le_rfl hYd
        have hold : evaluate a γ v (eraseBlocks [j])=v.support*evaluate a γ v j.2 := by
          rw [evaluate_blocks]
          simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one,hg,Rep.support]
        have hbe' : ‖τ.toPreGNS (average e τ hτ htr hfaith (w (γ j.1)*evaluate a γ v j.2)-
            c*average e τ hτ htr hfaith q)‖≤θ*(τ q).re := by
          simpa only [hg,show w 1=q from hw] using hbe
        have hh := singleton_cancellation_bound e τ hτ htr hfaith h1 v hp hp0 hpv hq hEq
          (evaluate a γ v j.2) (average e τ hτ htr hfaith (w (γ j.1)*evaluate a γ v j.2))
          (ε j.2.length) δ θ hEn hδ hpδ hY hbe'
        rw [hold]
        have hθL := mul_le_mul_of_nonneg_right hL1 hθ
        have heq : 2*ε j.2.length/δ=2*(ε j.2.length/δ) := by ring
        rw [heq]
        nlinarith
      · rw [ite_eq_right hg,zero_smul,add_zero]
        have hk := hkill [j.1] (by simp only [List.length_cons,List.length_nil]; rw [hlen] at hL; omega)
          (by simpa using hg)
        simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one] at hk
        rw [hk,mul_zero,sub_zero] at hbe
        have hθL := mul_le_mul_of_nonneg_right hL1 hθ
        have heq : 2*ε j.2.length/δ=2*(ε j.2.length/δ) := by ring
        rw [heq]
        nlinarith
end PopaCenter

end

end OAI
