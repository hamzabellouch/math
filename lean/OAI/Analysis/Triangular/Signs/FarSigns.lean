import OAI.Analysis.Triangular.Signs.SineGlobal
import OAI.Analysis.Triangular.Construction.FarCurvature
import OAI.Analysis.Triangular.Signs.NearSigns

namespace OAI

noncomputable section
open Set
namespace AtomicTriangular.Construction
open AtomicTriangular.FiniteCertificate
lemma deletedSecond_identity (f : ℝ → ℝ) (m s : ℝ) :
    f s=f m+deriv f m*(s-m)+(s-m)^2*deletedSecond f m s := by
  by_cases hsm : s=m
  · simp [hsm]
  · rw [deletedSecond,ite_eq_right hsm]
    field_simp [sub_ne_zero.mpr hsm]
    ring
lemma actualJ0_jets (side : Fin 2) {z : ℝ} (hz : 0<z) (hzB : z ≤ Z) (n : Node) :
    actualJ0 side z hz hzB n.val=actualJ side z hz hzB n.val ∧
      deriv (actualJ0 side z hz hzB) n.val=deriv (actualJ side z hz hzB) n.val := by
  have hp := realP_jet_zero n
  have hv := congrFun (actualJ_decompose side hz hzB) (n.val:ℝ)
  have hd := ((realP_contDiff.differentiable (by norm_num) (n.val:ℝ)).hasDerivAt.const_mul (sideConstant side)).add
    ((actualJ0_contDiff side hz hzB).differentiable (by norm_num) (n.val:ℝ)).hasDerivAt
  change HasDerivAt (sideConstant side • realP+actualJ0 side z hz hzB) _ _ at hd
  rw [←actualJ_decompose side hz hzB] at hd
  constructor
  · simpa only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,hp.1,mul_zero,zero_add] using hv.symm
  · simpa only [hp.2,mul_zero,zero_add] using hd.deriv.symm
def farK (i : Fin 5) : ℝ :=
  (301/100)*finiteCurvatureEnvelope i+(3/1000000000)*tailCurvatureEnvelope i+(3/500)*(2/1000)
lemma actualJ0_deleted (side : Fin 2) {z s : ℝ} (hz : 0<z) (hzB : z ≤ Z)
    (n : Node) (i : Fin 5) (hs : curvaturePoint i ≤ s) (hm : curvaturePoint i ≤ (n.val:ℝ))
    (hs14 : 29/2 ≤ s) (hm14 : 29/2 ≤ (n.val:ℝ)) :
    |deletedSecond (actualJ0 side z hz hzB) n.val s| ≤ farK i := by
  have hh := deletedSecond_bound ((actualJ0_contDiff side hz hzB).of_le (by norm_num))
    (m:=(n.val:ℝ)) (s:=s) (C:=2*farK i) (by
      intro t ht
      have hi : curvaturePoint i ≤ t := (le_min hm hs).trans ht.1
      have h14 : 29/2 ≤ t := (le_min hm14 hs14).trans ht.1
      have hc := actualJ0_curvature side hz hzB i hi h14
      change |iteratedDeriv 2 (actualJ0 side z hz hzB) t|/2 ≤ farK i at hc
      linarith)
  simpa using hh
lemma far_signs_of_barrier {z s : ℝ} (hz : 0<z) (hzB : z ≤ Z)
    (n : Node) (i : Fin 5) (hs : curvaturePoint i ≤ s) (hm : curvaturePoint i ≤ (n.val:ℝ))
    (hs14 : 29/2 ≤ s) (hm14 : 29/2 ≤ (n.val:ℝ))
    (hb : farK i*(s-n.val)^2 ≤ (3/500)*realP s) :
    actualJ 0 z hz hzB s ≤ gaussianG z s ∧ 0 ≤ actualJ 1 z hz hzB s := by
  have hj := actual_interpolation hz hzB n
  have hj0 := actualJ0_jets 0 hz hzB n
  have hj1 := actualJ0_jets 1 hz hzB n
  have h0 := mul_le_mul_of_nonneg_left (abs_le.mp (actualJ0_deleted 0 hz hzB n i hs hm hs14 hm14)).2 (sq_nonneg (s-n.val))
  have h1 := mul_le_mul_of_nonneg_left (abs_le.mp (actualJ0_deleted 1 hz hzB n i hs hm hs14 hm14)).1 (sq_nonneg (s-n.val))
  have hg := mul_nonneg (sq_nonneg (s-n.val)) (gaussian_deleted_nonneg hz n.val (s-n.val))
  simp only [add_sub_cancel] at hg
  have he0 := deletedSecond_identity (actualJ0 0 z hz hzB) n.val s
  rw [hj0.1,hj0.2,hj.1,hj.2.1] at he0
  have he1 := deletedSecond_identity (actualJ0 1 z hz hzB) n.val s
  rw [hj1.1,hj1.2,hj.2.2.1,hj.2.2.2] at he1
  have heG := deletedSecond_identity (gaussianG z) n.val s
  have hd0 := congrFun (actualJ_decompose 0 hz hzB) s
  have hd1 := congrFun (actualJ_decompose 1 hz hzB) s
  norm_num [Pi.add_apply,Pi.smul_apply,smul_eq_mul,sideConstant] at hd0 hd1
  constructor <;> nlinarith
lemma middle_signs {z s : ℝ} (hz : 0<z) (hzB : z ≤ Z) (hs : s∈Icc (29/2) 23) :
    actualJ 0 z hz hzB s ≤ gaussianG z s ∧ 0 ≤ actualJ 1 z hz hzB s := by
  obtain ⟨m,hm,hP⟩ := realP_middle_lower hs
  have hn : 0 < m ∧ m%36∈residues := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with rfl|rfl|rfl <;> norm_num [residues]
  have hm14 : 29/2 ≤ (m:ℝ) := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with rfl|rfl|rfl <;> norm_num
  apply far_signs_of_barrier hz hzB ⟨m,hn⟩ 3 hs.1 hm14 hs.1 hm14
  have hK : farK 3=(140109/10000000:ℝ) := by
    change (301/100:ℝ)*(465/100000)+(3/1000000000)*800+(3/500)*(2/1000)=_
    norm_num
  change farK 3*(s-m)^2 ≤ (3/500)*realP s
  rw [hK]
  nlinarith [sq_nonneg (s-m)]
lemma later_signs {z s : ℝ} (hz : 0<z) (hzB : z ≤ Z) (hs : 23 ≤ s) :
    actualJ 0 z hz hzB s ≤ gaussianG z s ∧ 0 ≤ actualJ 1 z hz hzB s := by
  obtain ⟨n,hn,hP⟩ := realP_far_lower hs
  have hm : (23:ℝ) ≤ n.val := by exact_mod_cast (show (23:ℤ) ≤ n.val by omega)
  apply far_signs_of_barrier hz hzB n 4 hs hm (by linarith) (by linarith)
  have hK : farK 4=(8363/100000000:ℝ) := by
    change (301/100:ℝ)*(23/1000000)+(3/1000000000)*800+(3/500)*(2/1000)=_
    norm_num
  rw [hK]
  nlinarith [sq_nonneg (s-n.val)]
theorem global_signs {z s : ℝ} (hz : 0<z) (hzB : z ≤ Z) (hs : 0 ≤ s) :
    actualJ 0 z hz hzB s ≤ gaussianG z s ∧ 0 ≤ actualJ 1 z hz hzB s := by
  by_cases h14 : s ≤ 29/2
  · exact near_signs hz hzB ⟨hs,h14⟩
  by_cases h23 : s ≤ 23
  · exact middle_signs hz hzB ⟨by linarith,h23⟩
  exact later_signs hz hzB (by linarith)
end AtomicTriangular.Construction
end

end OAI
