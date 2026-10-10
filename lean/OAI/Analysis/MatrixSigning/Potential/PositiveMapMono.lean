import Mathlib
import OAI.Analysis.MatrixSigning.Potential.Lagrangian
import OAI.Analysis.MatrixSigning.Matrices.RealTraceSum
import OAI.Analysis.MatrixSigning.Potential.SchurBlock
import OAI.Analysis.MatrixSigning.Matrices.OperatorNorm

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

lemma positiveMap_mono (η : H d →L[ℝ] H d)
    (hη : ∀ A ∈ psdCone d,η A ∈ psdCone d) {A B : H d} (h : A ≤ B) : η A ≤ η B := by
  apply sub_nonneg.mp
  rw [← map_sub]
  exact psd_nonneg (hη (B-A) ((mem_psd_iff_nonneg _).mpr (sub_nonneg.mpr h)))

lemma invH_order_bound {X : H d} {r : ℝ} (hr : 0 < r)
    (h : r • (Hermitian.one : H d) ≤ X) : invH X ≤ r⁻¹ • Hermitian.one := by
  have hX := pd_of_lower hr h
  have hi := inverse_antitone (scalar_posDef hr) hX h
  change invH X ≤ invH (r • (Hermitian.one : H d)) at hi
  rwa [invH_scalar] at hi

lemma value_center_neighborhood (S : H d) (η : H d →L[ℝ] H d)
    (hη : ∀ A ∈ psdCone d,η A ∈ psdCone d)
    (hη1 : η Hermitian.one ≤ (384:ℝ) • Hermitian.one)
    (hSlo : -(1:ℝ) • (Hermitian.one : H d) ≤ S)
    (hShi : S ≤ (1:ℝ) • (Hermitian.one : H d))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (z : Point d)
    (ht : |z.1-50| ≤ 1/1000)
    (hX : ‖z.2.1-(1/20:ℝ) • (Hermitian.one : H d)‖ ≤ 1/1000)
    (hY : ‖z.2.2-(1/20:ℝ) • (Hermitian.one : H d)‖ ≤ 1/1000) :
    z ∈ valueSpectrahedron ε S η := by
  have bounds (X : H d) (hX : ‖X-(1/20:ℝ) • (Hermitian.one : H d)‖ ≤ 1/1000) :
      (1/21:ℝ) • (Hermitian.one : H d) ≤ X ∧ X ≤ (51/1000:ℝ) • Hermitian.one := by
    obtain ⟨hl,hu⟩ := ball_order_bounds X ((1/20:ℝ) • (Hermitian.one : H d)) hX
    have hl' : ((1/20-1/1000:ℝ) • (Hermitian.one : H d)) ≤ X := by
      convert hl using 1
      first | rfl | module
    rw [← add_smul] at hu
    exact ⟨(scalar_one_mono (by norm_num : (1/21:ℝ)≤1/20-1/1000)).trans hl',by
      convert hu using 1
      first | rfl | module⟩
  obtain ⟨hXlo,hXhi⟩ := bounds z.2.1 hX
  obtain ⟨hYlo,hYhi⟩ := bounds z.2.2 hY
  have htlo : (49:ℝ) ≤ z.1 := by have := (abs_le.mp ht).1; linarith
  have hthi : z.1 ≤ (51:ℝ) := by have := (abs_le.mp ht).2; linarith
  have hXpd := pd_of_lower (by norm_num : (0:ℝ)<1/21) hXlo
  have hYpd := pd_of_lower (by norm_num : (0:ℝ)<1/21) hYlo
  have hXinv : invH z.2.1 ≤ (21:ℝ) • Hermitian.one := by
    simpa using invH_order_bound (by norm_num : (0:ℝ)<1/21) hXlo
  have hYinv : invH z.2.2 ≤ (21:ℝ) • Hermitian.one := by
    simpa using invH_order_bound (by norm_num : (0:ℝ)<1/21) hYlo
  have hmap (X : H d) (hX : X ≤ (51/1000:ℝ) • Hermitian.one) :
      η X ≤ (20:ℝ) • Hermitian.one := by
    calc
      _ ≤ η ((51/1000:ℝ) • Hermitian.one) := positiveMap_mono η hη hX
      _ = (51/1000:ℝ) • η Hermitian.one := map_smul η _ _
      _ ≤ (51/1000:ℝ) • ((384:ℝ) • Hermitian.one) := smul_order hη1 (by norm_num)
      _ ≤ (20:ℝ) • Hermitian.one := by rw [smul_smul]; exact scalar_one_mono (by norm_num)
  have hfit : (42:ℝ) • (Hermitian.one : H d) ≤ z.1 • Hermitian.one := scalar_one_mono (by linarith)
  have hminus : -S ≤ (1:ℝ) • (Hermitian.one : H d) := by
    convert neg_le_neg hSlo using 1
    first | rfl | module
  have hf : z ∈ feasible S η := by
    apply (feasible_iff S η z).mpr
    refine ⟨hXpd,hYpd,?_,?_⟩
    · have hh := add_le_add (add_le_add hXinv hShi) (hmap z.2.2 hYhi)
      apply le_trans hh
      convert hfit using 1
      first | rfl | module
    · have hh := add_le_add (add_le_add hYinv hminus) (hmap z.2.1 hXhi)
      change invH z.2.2 + -S + η z.2.1 ≤ _
      apply le_trans hh
      convert hfit using 1
      first | rfl | module
  have hlo : (1/400:ℝ) • (Hermitian.one : H d) ≤ (1/21:ℝ) • Hermitian.one := scalar_one_mono (by norm_num)
  have hr : (51/1000:ℝ) ≤ 200/ε := by
    apply (le_div_iff₀ hε).mpr
    nlinarith
  have hup := scalar_one_mono (d := d) hr
  apply (mem_valueSpectrahedron ε S η z).mpr
  exact ⟨⟨⟨by linarith,by linarith⟩,⟨hlo.trans hXlo,hXhi.trans hup⟩,
    ⟨hlo.trans hYlo,hYhi.trans hup⟩⟩,hf⟩

lemma convex_feasible (S : H d) (η : H d →L[ℝ] H d) : Convex ℝ (feasible S η) := by
  intro z hz w hw a b ha hb hab
  have hres := residual_coneConvex S η z hz.1 w hw.1 a b ha hb hab
  refine ⟨convex_domain hz.1 hw.1 ha hb hab,?_,?_⟩
  · have he : (residual S η (a • z+b • w)).1 ≤ a • (residual S η z).1+b • (residual S η w).1 := by
      exact sub_nonneg.mp (psd_nonneg hres.1)
    have hh := add_le_add (smul_order hz.2.1 ha) (smul_order hw.2.1 hb)
    exact he.trans (by simpa only [smul_zero,add_zero] using hh)
  · have he : (residual S η (a • z+b • w)).2 ≤ a • (residual S η z).2+b • (residual S η w).2 := by
      exact sub_nonneg.mp (psd_nonneg hres.2)
    have hh := add_le_add (smul_order hz.2.2 ha) (smul_order hw.2.2 hb)
    exact he.trans (by simpa only [smul_zero,add_zero] using hh)

lemma convex_orderBox_H (r s : ℝ) :
    Convex ℝ {X : H d | r • Hermitian.one ≤ X ∧ X ≤ s • Hermitian.one} := by
  intro X hX Y hY a b ha hb hab
  constructor
  · have hh := add_le_add (smul_order hX.1 ha) (smul_order hY.1 hb)
    have he : a • (r • (Hermitian.one : H d))+b • (r • Hermitian.one) = r • Hermitian.one := by
      rw [← add_smul,hab,one_smul]
    rwa [he] at hh
  · have hh := add_le_add (smul_order hX.2 ha) (smul_order hY.2 hb)
    have he : a • (s • (Hermitian.one : H d))+b • (s • Hermitian.one) = s • Hermitian.one := by
      rw [← add_smul,hab,one_smul]
    rwa [he] at hh

lemma convex_oracleBox (ε : ℝ) : Convex ℝ {z : Point d | oracleBox ε z} := by
  intro z hz w hw a b ha hb hab
  exact ⟨convex_Icc (0:ℝ) 100 hz.1 hw.1 ha hb hab,
    convex_orderBox_H _ _ hz.2.1 hw.2.1 ha hb hab,
    convex_orderBox_H _ _ hz.2.2 hw.2.2 ha hb hab⟩

lemma convex_valueSpectrahedron (ε : ℝ) (S : H d) (η : H d →L[ℝ] H d) :
    Convex ℝ (valueSpectrahedron ε S η) := by
  have he : valueSpectrahedron ε S η = {z | oracleBox ε z} ∩ feasible S η := by
    ext z
    exact mem_valueSpectrahedron ε S η z
  rw [he]
  exact (convex_oracleBox ε).inter (convex_feasible S η)

end
end CurrentKS.Variational

end OAI
