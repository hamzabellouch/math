import Mathlib
import OAI.GroupTheory.SimpleAmenable.Arithmetic.PolygonArithmetic

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
open scoped commutatorElement
open scoped commutatorElement
section QuadraticTiles
open Classical Module MeasureTheory
open scoped QuadraticAlgebra

theorem cutUnit_abs_norm {u : CutRing} (hu : IsUnit u) :
    |ordinary u*conjugate u|=1 := by
  rw [cut_norm_identity,← Int.cast_abs]
  have h := (QuadraticAlgebra.isUnit_iff_norm_isUnit.mp hu)
  rcases Int.isUnit_iff.mp h with h|h <;> simp [h]

theorem cutTau_sub_one_isUnit : IsUnit (cutTau-1) := by
  apply QuadraticAlgebra.isUnit_iff_norm_isUnit.mpr
  norm_num [cutTau,QuadraticAlgebra.norm_def]

theorem balanced_cutUnit {L : ℝ} (hL : 1≤L) :
    ∃u : CutRing,IsUnit u ∧ |ordinary u| ≤ 2/L ∧ |conjugate u| ≤ L := by
  obtain ⟨k,hk,hk'⟩ := exists_nat_pow_near hL Real.one_lt_goldenRatio
  let u : CutRing := (cutTau-1)^k
  have hp : 0<Real.goldenRatio^k := pow_pos Real.goldenRatio_pos _
  have ho : ordinary u=(Real.goldenRatio^k)⁻¹ := by
    simp only [u,map_pow,map_sub,ordinary_cutTau,map_one]
    rw [← inv_pow]
    congr 1
    rw [Real.inv_goldenRatio]
    linarith [Real.goldenRatio_add_goldenConj]
  have hc : |conjugate u|=Real.goldenRatio^k := by
    simp only [u,map_pow,map_sub,conjugate_cutTau,map_one,abs_pow]
    congr 1
    rw [abs_of_neg (by linarith [Real.goldenConj_neg] : Real.goldenConj-1<0)]
    linarith [Real.goldenRatio_add_goldenConj]
  refine ⟨u,cutTau_sub_one_isUnit.pow k,?_,by simpa only [hc] using hk⟩
  rw [ho,abs_of_pos (inv_pos.mpr hp)]
  have hL₀ : 0<L := lt_of_lt_of_le zero_lt_one hL
  apply (le_div_iff₀ hL₀).mpr
  have hh : L<2*Real.goldenRatio^k := by
    rw [pow_succ] at hk'
    nlinarith [Real.goldenRatio_lt_two]
  have he := mul_le_mul_of_nonneg_left hh.le (inv_nonneg.mpr hp.le)
  have hh' : (Real.goldenRatio^k)⁻¹*(2*Real.goldenRatio^k)=2 := by field_simp
  rw [hh'] at he
  exact he

noncomputable def quadraticScaledMatrix (u : CutRing) (d s t : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![ordinary u/(d*s),ordinary u*Real.goldenRatio/(d*s);
     conjugate u/(d*t),conjugate u*Real.goldenConj/(d*t)]

theorem quadraticScaledMatrix_det (u : CutRing) (d s t : ℝ) :
    (quadraticScaledMatrix u d s t).det=
      ordinary u*conjugate u*(Real.goldenConj-Real.goldenRatio)/(d^2*s*t) := by
  simp only [quadraticScaledMatrix,Matrix.det_fin_two,Matrix.of_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  ring

theorem quadraticScaledMatrix_det_ne {u : CutRing} (hu : IsUnit u)
    {d s t : ℝ} (hd : 0<d) (hs : 0<s) (ht : 0<t) :
    (quadraticScaledMatrix u d s t).det≠0 := by
  rw [quadraticScaledMatrix_det]
  apply div_ne_zero
  · apply mul_ne_zero
    · exact (abs_ne_zero.mp (by rw [cutUnit_abs_norm hu]; norm_num))
    · linarith [Real.goldenRatio_pos,Real.goldenConj_neg]
  · positivity

noncomputable def quadraticScaledBasis {u : CutRing} (hu : IsUnit u)
    {d s t : ℝ} (hd : 0<d) (hs : 0<s) (ht : 0<t) : Basis (Fin 2) ℝ (Fin 2 → ℝ) :=
  (Pi.basisFun ℝ (Fin 2)).map ((quadraticScaledMatrix u d s t).toLinearEquiv
    (Pi.basisFun ℝ (Fin 2)) (isUnit_iff_ne_zero.mpr (quadraticScaledMatrix_det_ne hu hd hs ht)))

theorem quadraticScaledBasis_apply {u : CutRing} (hu : IsUnit u)
    {d s t : ℝ} (hd : 0<d) (hs : 0<s) (ht : 0<t) (i j : Fin 2) :
    quadraticScaledBasis hu hd hs ht i j=quadraticScaledMatrix u d s t j i := by
  simp only [quadraticScaledBasis,Basis.map_apply,Matrix.toLinearEquiv_apply,
    Matrix.toLin_self]
  fin_cases j <;> simp [Pi.basisFun_apply,Fin.sum_univ_two]

theorem quadraticScaledBasis_volume {u : CutRing} (hu : IsUnit u)
    {d s t : ℝ} (hd : 0<d) (hs : 0<s) (ht : 0<t) :
    volume.real (ZSpan.fundamentalDomain (quadraticScaledBasis hu hd hs ht))=
      Real.sqrt 5/(d^2*s*t) := by
  rw [ZSpan.volume_real_fundamentalDomain]
  have he : Matrix.of (quadraticScaledBasis hu hd hs ht)=
      (quadraticScaledMatrix u d s t).transpose := by
    ext i j
    exact quadraticScaledBasis_apply hu hd hs ht i j
  rw [he,Matrix.det_transpose,quadraticScaledMatrix_det,abs_div,abs_mul,cutUnit_abs_norm hu,
    one_mul,abs_of_pos (by positivity : 0<d^2*s*t)]
  congr 1
  rw [abs_of_neg (by linarith [Real.goldenRatio_pos,Real.goldenConj_neg])]
  linarith [Real.goldenRatio_sub_goldenConj]

noncomputable def quadraticScaledEmbedding (d s t : ℝ) : CutRing →ₗ[ℤ] (Fin 2 → ℝ) where
  toFun z := ![ordinary z/(d*s),conjugate z/(d*t)]
  map_add' z w := by ext i; fin_cases i <;> simp [add_div]
  map_smul' n z := by ext i; fin_cases i <;> simp [mul_div_assoc]

theorem quadraticScaledEmbedding_injective {d s t : ℝ}
    (hd : 0<d) (hs : 0<s) : Function.Injective (quadraticScaledEmbedding d s t) := by
  intro z w hh
  apply ordinary_injective
  have h := congrFun hh 0
  exact (div_left_inj' (mul_pos hd hs).ne').mp h

theorem quadraticScaledBasis_zero {u : CutRing} (hu : IsUnit u)
    {d s t : ℝ} (hd : 0<d) (hs : 0<s) (ht : 0<t) :
    quadraticScaledBasis hu hd hs ht 0=quadraticScaledEmbedding d s t u := by
  ext i
  rw [quadraticScaledBasis_apply]
  fin_cases i <;> rfl

theorem quadraticScaledBasis_one {u : CutRing} (hu : IsUnit u)
    {d s t : ℝ} (hd : 0<d) (hs : 0<s) (ht : 0<t) :
    quadraticScaledBasis hu hd hs ht 1=quadraticScaledEmbedding d s t (u*cutTau) := by
  ext i
  rw [quadraticScaledBasis_apply]
  fin_cases i <;> simp [quadraticScaledMatrix,quadraticScaledEmbedding]

theorem quadraticScaledBasis_span {u : CutRing} (hu : IsUnit u)
    {d s t : ℝ} (hd : 0<d) (hs : 0<s) (ht : 0<t) :
    Submodule.span ℤ (Set.range (quadraticScaledBasis hu hd hs ht))=
      (quadraticScaledEmbedding d s t).range := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    fin_cases i
    · change quadraticScaledBasis hu hd hs ht 0∈_
      rw [quadraticScaledBasis_zero]; exact LinearMap.mem_range_self _ _
    · change quadraticScaledBasis hu hd hs ht 1∈_
      rw [quadraticScaledBasis_one]; exact LinearMap.mem_range_self _ _
  · rintro _ ⟨z,rfl⟩
    have huu := hu
    obtain ⟨U,hU⟩ := huu
    let w : CutRing := (↑(U⁻¹):CutRing)*z
    have hz : u*w=z := by simp [w,← hU,← mul_assoc]
    have hw' : w=(w.re:CutRing)+(w.im:CutRing)*cutTau := by
      ext <;> simp [cutTau]
    have he : quadraticScaledEmbedding d s t z=
        w.re • quadraticScaledBasis hu hd hs ht 0+
        w.im • quadraticScaledBasis hu hd hs ht 1 := by
      rw [quadraticScaledBasis_zero,quadraticScaledBasis_one,← LinearMap.map_smul,
        ← LinearMap.map_smul,← map_add]
      congr 1
      rw [← hz,zsmul_eq_mul,zsmul_eq_mul]
      conv_lhs => rhs; rw [hw']
      ring
    rw [he]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0,rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1,rfl⟩))

theorem quadraticScaledTile_bound {u : CutRing} (hu : IsUnit u)
    {d s t : ℝ} (hd : 0<d) (hs : 0<s) (ht : 0<t)
    (x : Fin 2 → ℝ) (hx : x∈ZSpan.fundamentalDomain (quadraticScaledBasis hu hd hs ht)) :
    |x 0| ≤ 3*|ordinary u|/(d*s) ∧ |x 1| ≤ 2*|conjugate u|/(d*t) := by
  let b := quadraticScaledBasis hu hd hs ht
  have hcoeff := (ZSpan.mem_fundamentalDomain b).mp hx
  have hx' : x=(b.repr x 0) • b 0+(b.repr x 1) • b 1 := by
    simpa only [Fin.sum_univ_two] using (b.sum_repr x).symm
  have hg : |Real.goldenRatio| ≤ 2 := by
    rw [abs_of_pos Real.goldenRatio_pos]; exact Real.goldenRatio_lt_two.le
  have hg' : |Real.goldenConj| ≤ 1 := by
    rw [abs_of_neg Real.goldenConj_neg]; linarith [Real.neg_one_lt_goldenConj]
  have hc (i : Fin 2) : |b.repr x i|≤1 := by
    rw [abs_of_nonneg (hcoeff i).1]; exact (hcoeff i).2.le
  have hcalc (a q c₀ c₁ R k : ℝ) (hR : 0<R) (hq : |q|≤k)
      (hc₀ : |c₀|≤1) (hc₁ : |c₁|≤1) :
      |c₀*(a/R)+c₁*(a*q/R)| ≤ (1+k)*|a|/R := by
    calc
      _ ≤ |c₀*(a/R)|+|c₁*(a*q/R)| := abs_add_le _ _
      _ = |c₀| *(|a|/R)+|c₁| *(|a| *|q|/R) := by
        simp only [abs_mul,abs_div,abs_of_pos hR]
      _ ≤ 1*(|a|/R)+1*(|a| *k/R) := by gcongr
      _ = _ := by ring
  rw [congrFun hx' 0,congrFun hx' 1]
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  change |(b.repr x 0)*b 0 0+(b.repr x 1)*b 1 0| ≤ _ ∧
    |(b.repr x 0)*b 0 1+(b.repr x 1)*b 1 1| ≤ _
  simp only [b,quadraticScaledBasis_apply,quadraticScaledMatrix,Matrix.of_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  constructor
  · simpa only [show (1:ℝ)+2=3 by norm_num] using
      hcalc (ordinary u) Real.goldenRatio (b.repr x 0) (b.repr x 1) (d*s) 2 (mul_pos hd hs) hg (hc 0) (hc 1)
  · simpa only [show (1:ℝ)+1=2 by norm_num] using
      hcalc (conjugate u) Real.goldenConj (b.repr x 0) (b.repr x 1) (d*t) 1 (mul_pos hd ht) hg' (hc 0) (hc 1)

end QuadraticTiles

end SimpleAmenable
end
end

end OAI
