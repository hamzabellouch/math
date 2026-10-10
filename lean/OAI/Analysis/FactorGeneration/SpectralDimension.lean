import OAI.Analysis.FactorGeneration.NormalDimension
import OAI.Analysis.FactorGeneration.SpectralApproximation

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Finite spectral weights of the constructed projection dimension obey an
operator-norm bound. No linear trace on noncommuting elements is assumed. -/
section
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

include hfinite in
theorem traceFreeDimension_finsetSum
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    {I : Type*} (q : I → AlgebraProjection M) (s : Finset I)
    (ho : ∀ i ∈ s, ∀ j ∈ s, i≠j → (q i).val*(q j).val=0) :
    traceFreeDimension hfactor hdiff (AlgebraProjection.finsetSum q s ho)=
      ∑ i ∈ s, traceFreeDimension hfactor hdiff (q i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hz : (AlgebraProjection.finsetSum q ∅ ho).val=0 := by simp [AlgebraProjection.finsetSum]
    simpa only [Finset.sum_empty,traceFreeDimension] using traceFreeDyadicSup_zero hfactor hdiff
      ⟨1,IsStarProjection.one _⟩ _ hunit hz
  | @insert i s hi ih =>
    have hos : ∀ j ∈ s, ∀ k ∈ s, j≠k → (q j).val*(q k).val=0 :=
      fun j hj k hk => ho j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk)
    let r := AlgebraProjection.finsetSum q s hos
    have hqr : (q i).val*r.val=0 := by
      change (q i).val*(∑ j ∈ s, (q j).val)=0
      rw [Finset.mul_sum]
      exact Finset.sum_eq_zero (fun j hj => ho i (Finset.mem_insert_self _ _) j
        (Finset.mem_insert_of_mem hj) (fun he => hi (he.symm ▸ hj)))
    have he : AlgebraProjection.finsetSum q (insert i s) ho=orthogonalSum (q i) r hqr := by
      apply Subtype.ext
      exact Finset.sum_insert hi
    rw [he,Finset.sum_insert hi]
    have hadd := traceFreeDyadicSup_orthogonal_add hfactor hdiff hfinite
      ⟨1,IsStarProjection.one _⟩ (q i) r hunit (one_mul _) (one_mul _) hqr
    change traceFreeDimension hfactor hdiff (orthogonalSum (q i) r hqr)=
      traceFreeDimension hfactor hdiff (q i)+traceFreeDimension hfactor hdiff r at hadd
    rw [hadd,ih hos]

include hfinite in
theorem traceFreeDimension_sum_of_total
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    {I : Type*} [Fintype I] (q : I → AlgebraProjection M)
    (ho : ∀ i j, i≠j → (q i).val*(q j).val=0)
    (p : AlgebraProjection M) (hp : ∑ i, (q i).val=p.val) :
    ∑ i, traceFreeDimension hfactor hdiff (q i)=traceFreeDimension hfactor hdiff p := by
  classical
  have he : AlgebraProjection.finsetSum q Finset.univ (fun i _ j _ => ho i j)=p := Subtype.ext hp
  rw [← he]
  exact (traceFreeDimension_finsetSum hfactor hdiff hfinite hunit q Finset.univ _).symm

include hfinite in
/-- A finite orthogonal spectral value has the required operator-norm bound. -/
theorem traceFreeDimension_spectralWeight_norm_le
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    {I : Type*} [Fintype I] (q : I → AlgebraProjection M)
    (ho : ∀ i j, i≠j → (q i).val*(q j).val=0) (c : I → ℂ) :
    ‖∑ i, c i*(traceFreeDimension hfactor hdiff (q i) : ℂ)‖ ≤
      ‖∑ i, c i • (q i).val‖ := by
  classical
  let a : M.toStarSubalgebra := ∑ i, c i • (q i).val
  have hpiece (i : I) : a*(q i).val=c i • (q i).val := by
    dsimp [a]
    rw [Finset.sum_mul]
    apply (Finset.sum_eq_single i ?_ ?_).trans
      (by rw [smul_mul_assoc,(q i).property.isIdempotentElem.eq])
    · intro j _ hji
      rw [smul_mul_assoc,ho j i hji,smul_zero]
    · intro h; exact (h (Finset.mem_univ i)).elim
  have hterm (i : I) : ‖c i*(traceFreeDimension hfactor hdiff (q i) : ℂ)‖ ≤
      ‖a‖*traceFreeDimension hfactor hdiff (q i) := by
    by_cases hz : (q i).val=0
    · have hD := traceFreeDyadicSup_zero hfactor hdiff ⟨1,IsStarProjection.one _⟩ (q i) hunit hz
      change traceFreeDimension hfactor hdiff (q i)=0 at hD
      simp only [hD,Complex.ofReal_zero,mul_zero,norm_zero,le_refl]
    · have hnorm := norm_mul_le a (q i).val
      rw [hpiece i,norm_smul] at hnorm
      have hpos : 0 < ‖(q i).val‖ := norm_pos_iff.mpr hz
      have hci : ‖c i‖ ≤ ‖a‖ := by nlinarith
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (traceFreeDimension_nonneg hfactor hdiff _)]
      exact mul_le_mul_of_nonneg_right hci (traceFreeDimension_nonneg hfactor hdiff _)
  have hdim : (∑ i, traceFreeDimension hfactor hdiff (q i)) ≤ 1 := by
    rw [← traceFreeDimension_finsetSum hfactor hdiff hfinite hunit q Finset.univ
      (fun i _ j _ => ho i j)]
    exact traceFreeDimension_le_one hfactor hdiff _
  calc
    ‖∑ i, c i*(traceFreeDimension hfactor hdiff (q i) : ℂ)‖ ≤
        ∑ i, ‖c i*(traceFreeDimension hfactor hdiff (q i) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖a‖*traceFreeDimension hfactor hdiff (q i) := Finset.sum_le_sum (fun i _ => hterm i)
    _ = ‖a‖*(∑ i, traceFreeDimension hfactor hdiff (q i)) := (Finset.mul_sum _ _ _).symm
    _ ≤ ‖a‖ := by nlinarith [norm_nonneg a]

include hfinite in
/-- In a fixed orthogonal partition, the spectral-value map is contractive. -/
theorem traceFreeDimension_spectralWeight_sub_norm_le
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    {I : Type*} [Fintype I] (q : I → AlgebraProjection M)
    (ho : ∀ i j, i≠j → (q i).val*(q j).val=0) (c d : I → ℂ) :
    ‖(∑ i, c i*(traceFreeDimension hfactor hdiff (q i) : ℂ))-
      (∑ i, d i*(traceFreeDimension hfactor hdiff (q i) : ℂ))‖ ≤
      ‖(∑ i, c i • (q i).val)-(∑ i, d i • (q i).val)‖ := by
  simpa only [sub_mul,sub_smul,Finset.sum_sub_distrib] using
    traceFreeDimension_spectralWeight_norm_le hfactor hdiff hfinite hunit q ho (fun i => c i-d i)

/-! Spectral dimension weights agree under common commuting refinements.
Contractivity is proved for two commuting partitions, not noncommuting inputs. -/
namespace CornerPartition
variable {p : AlgebraProjection M} (Q R : CornerPartition p)
variable (hc : ∀ i j, Commute (Q.piece i).val (R.piece j).val)

include hfinite in
theorem dimension_joint_row (hunit : (1 : M.toStarSubalgebra) ≠ 0) (i : Fin Q.size) :
    ∑ j, traceFreeDimension hfactor hdiff (Q.jointPiece R hc (i,j))=
      traceFreeDimension hfactor hdiff (Q.piece i) := by
  apply traceFreeDimension_sum_of_total hfactor hdiff hfinite hunit
    (fun j => Q.jointPiece R hc (i,j))
    (fun j k hjk => Q.jointPiece_orthogonal R hc (i,j) (i,k) (fun h => hjk (congrArg Prod.snd h)))
  change (∑ j, (Q.piece i).val*(R.piece j).val)=(Q.piece i).val
  rw [← Finset.mul_sum,R.total,projection_mul_of_le (Q.piece_le i)]

include hfinite in
theorem dimension_joint_column (hunit : (1 : M.toStarSubalgebra) ≠ 0) (j : Fin R.size) :
    ∑ i, traceFreeDimension hfactor hdiff (Q.jointPiece R hc (i,j))=
      traceFreeDimension hfactor hdiff (R.piece j) := by
  apply traceFreeDimension_sum_of_total hfactor hdiff hfinite hunit
    (fun i => Q.jointPiece R hc (i,j))
    (fun i k hik => Q.jointPiece_orthogonal R hc (i,j) (k,j) (fun h => hik (congrArg Prod.fst h)))
  change (∑ i, (Q.piece i).val*(R.piece j).val)=(R.piece j).val
  rw [← Finset.sum_mul,Q.total]
  exact R.piece_le j

include hfinite in
theorem dimension_weight_joint_left (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (c : Fin Q.size → ℂ) :
    (∑ a : Fin Q.size × Fin R.size,
      c a.1*(traceFreeDimension hfactor hdiff (Q.jointPiece R hc a) : ℂ))=
        ∑ i, c i*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ) := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only
  rw [← Finset.mul_sum,← Complex.ofReal_sum,dimension_joint_row hfactor hdiff hfinite Q R hc hunit]

include hfinite in
theorem dimension_weight_joint_right (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (c : Fin R.size → ℂ) :
    (∑ a : Fin Q.size × Fin R.size,
      c a.2*(traceFreeDimension hfactor hdiff (Q.jointPiece R hc a) : ℂ))=
        ∑ i, c i*(traceFreeDimension hfactor hdiff (R.piece i) : ℂ) := by
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  dsimp only
  rw [← Finset.mul_sum,← Complex.ofReal_sum,dimension_joint_column hfactor hdiff hfinite Q R hc hunit]

include hfinite hc in
/-- Changing between two commuting partitions preserves the norm estimate. -/
theorem dimension_weight_cross_norm_le (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (c : Fin Q.size → ℂ) (d : Fin R.size → ℂ) :
    ‖(∑ i, c i*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ))-
      (∑ j, d j*(traceFreeDimension hfactor hdiff (R.piece j) : ℂ))‖ ≤
      ‖(∑ i, c i • (Q.piece i).val)-(∑ j, d j • (R.piece j).val)‖ := by
  have h := traceFreeDimension_spectralWeight_sub_norm_le hfactor hdiff hfinite hunit
    (Q.jointPiece R hc) (Q.jointPiece_orthogonal R hc) (fun a => c a.1) (fun a => d a.2)
  rwa [Q.dimension_weight_joint_left hfactor hdiff hfinite R hc hunit c,
    Q.dimension_weight_joint_right hfactor hdiff hfinite R hc hunit d,
    Q.joint_sum_left R hc c,Q.joint_sum_right R hc d] at h

include hfinite hc in
theorem dimension_weight_eq_of_commuting_sums_eq (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (c : Fin Q.size → ℂ) (d : Fin R.size → ℂ)
    (he : (∑ i, c i • (Q.piece i).val)=(∑ j, d j • (R.piece j).val)) :
    (∑ i, c i*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ))=
      (∑ j, d j*(traceFreeDimension hfactor hdiff (R.piece j) : ℂ)) := by
  have h := Q.dimension_weight_cross_norm_le hfactor hdiff hfinite R hc hunit c d
  rw [he,sub_self,norm_zero] at h
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))

end CornerPartition

end

/-! Construct the unique real spectral dimension value of each self-adjoint
operator by norm approximation. Global noncommuting additivity is not asserted. -/
section
open Filter
open scoped BigOperators Topology
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

/-- Approximation specification, not an assumed linear trace. -/
def IsDimensionSpectralValue (x : M.toStarSubalgebra) (t : ℂ) : Prop :=
  ∀ (Q : CornerPartition ⟨1,IsStarProjection.one _⟩) (c : Fin Q.size → ℂ),
    (∀ i, Commute (Q.piece i).val x) →
      ‖t-∑ i, c i*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ)‖ ≤
        ‖x-∑ i, c i • (Q.piece i).val‖

include hfinite in
/-- Actual finite spectral approximants are Cauchy in their dimension values,
and their real limit controls every commuting spectral approximation. -/
theorem traceFreeDimension_exists_spectral_value
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    ∃ t : ℂ, t.im=0 ∧ IsDimensionSpectralValue hfactor hdiff x t := by
  classical
  have happrox (n : ℕ) :
      ∃ (Q : CornerPartition (⟨1,IsStarProjection.one _⟩ : AlgebraProjection M))
        (c : Fin Q.size → ℝ),
        (∀ y : M.toStarSubalgebra, Commute x y → ∀ i, Commute (Q.piece i).val y) ∧
        ‖x-∑ i, (c i : ℂ) • (Q.piece i).val‖ < 1/2^n := by
    obtain ⟨Q,c,_,hQ,herr⟩ := exists_finite_spectral_approximation_preserving_commutant
      ⟨1,IsStarProjection.one _⟩ x hx (1/2^n) (by positivity)
    exact ⟨Q,c,fun y hy => hQ y hy (Commute.one_left y),by simpa only [one_mul,mul_one] using herr⟩
  choose Q c hQ herr using happrox
  let f (n : ℕ) : ℂ := ∑ i, (c n i : ℂ)*(traceFreeDimension hfactor hdiff ((Q n).piece i) : ℂ)
  let a (n : ℕ) : M.toStarSubalgebra := ∑ i, (c n i : ℂ) • ((Q n).piece i).val
  have hbound (n : ℕ) (R : CornerPartition (⟨1,IsStarProjection.one _⟩ : AlgebraProjection M))
      (d : Fin R.size → ℂ) (hR : ∀ j, Commute (R.piece j).val x) :
      ‖f n-∑ j, d j*(traceFreeDimension hfactor hdiff (R.piece j) : ℂ)‖ ≤
        1/2^n+‖x-∑ j, d j • (R.piece j).val‖ := by
    have hc (i : Fin (Q n).size) (j : Fin R.size) :
        Commute ((Q n).piece i).val (R.piece j).val := hQ n _ (hR j).symm i
    have h := (Q n).dimension_weight_cross_norm_le hfactor hdiff hfinite R hc hunit
      (fun i => (c n i : ℂ)) d
    refine h.trans ?_
    have htri := dist_triangle (a n) x (∑ j, d j • (R.piece j).val)
    simp only [dist_eq_norm] at htri
    rw [norm_sub_rev (a n) x] at htri
    exact htri.trans (add_le_add (herr n).le le_rfl)
  have heps : Tendsto (fun n : ℕ => (1 : ℝ)/2^n) atTop (𝓝 0) := by
    simpa only [one_div_pow] using tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num : (1/2 : ℝ)<1)
  have hf : CauchySeq f := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := eventually_atTop.mp (heps.eventually (gt_mem_nhds (half_pos hε)))
    refine ⟨N,?_⟩
    intro m hm n hn
    rw [dist_eq_norm]
    have h := hbound m (Q n) (fun i => (c n i : ℂ)) (hQ n x (Commute.refl x))
    have he := herr n
    have hm' := hN m hm
    have hn' := hN n hn
    change ‖f m-f n‖ ≤ _ at h
    linarith
  obtain ⟨t,ht⟩ := cauchySeq_tendsto_of_complete hf
  have him (n : ℕ) : (f n).im=0 := by simp [f]
  refine ⟨t,?_,?_⟩
  · have hi := Complex.continuous_im.tendsto t |>.comp ht
    exact tendsto_nhds_unique hi (by
      change Tendsto (fun n => (f n).im) atTop (𝓝 0)
      simpa only [him] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))
  · intro R d hR
    apply le_of_tendsto_of_tendsto' ((ht.sub_const _).norm)
      (by simpa only [zero_add] using heps.add_const ‖x-∑ j, d j • (R.piece j).val‖)
    exact fun n => hbound n R d hR

theorem IsDimensionSpectralValue.unique
    {x : M.toStarSubalgebra} (hx : IsSelfAdjoint x) {s t : ℂ}
    (hs : IsDimensionSpectralValue hfactor hdiff x s)
    (ht : IsDimensionSpectralValue hfactor hdiff x t) : s=t := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply eq_of_all_dyadic_errors
  intro n
  obtain ⟨Q,c,_,hQ,herr⟩ := exists_finite_spectral_approximation_preserving_commutant
    ⟨1,IsStarProjection.one _⟩ x hx (1/2^n) (by positivity)
  have hcomm := hQ x (Commute.refl x) (Commute.one_left x)
  have hs' := hs Q (fun i => (c i : ℂ)) hcomm
  have ht' := ht Q (fun i => (c i : ℂ)) hcomm
  simp only [one_mul,mul_one] at herr
  let w : ℂ := ∑ i, (c i : ℂ)*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ)
  have htri := dist_triangle s w t
  simp only [dist_eq_norm] at htri
  rw [norm_sub_rev w t] at htri
  dsimp only [w] at htri
  have hnorm : ‖s-t‖ ≤ 2/2^n := by
    rw [show (2 : ℝ)/2^n=2*(1/2^n) by ring]
    linarith
  simpa only [sub_zero,abs_of_nonneg (norm_nonneg _)] using hnorm

/-- This is a constructed scalar value on self-adjoint operators; it is not
yet packaged as a linear functional. -/
def dimensionSpectralValue (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) : ℂ :=
  (traceFreeDimension_exists_spectral_value hfactor hdiff hfinite hunit x hx).choose

theorem dimensionSpectralValue_spec (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    (dimensionSpectralValue hfactor hdiff hfinite hunit x hx).im=0 ∧
      IsDimensionSpectralValue hfactor hdiff x
        (dimensionSpectralValue hfactor hdiff hfinite hunit x hx) :=
  (traceFreeDimension_exists_spectral_value hfactor hdiff hfinite hunit x hx).choose_spec

end

/-! The constructed spectral value is bounded and extends the actual
projection dimension. These laws do not assert noncommuting additivity. -/
section
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

theorem IsDimensionSpectralValue.norm_le {x : M.toStarSubalgebra} {t : ℂ}
    (ht : IsDimensionSpectralValue hfactor hdiff x t) : ‖t‖ ≤ ‖x‖ := by
  have h := ht (CornerPartition.single ⟨1,IsStarProjection.one _⟩) (fun _ => 0)
    (fun _ => Commute.one_left x)
  simpa only [zero_mul,zero_smul,Finset.sum_const_zero,sub_zero] using h

theorem IsDimensionSpectralValue.on_projection (p : AlgebraProjection M) {t : ℂ}
    (ht : IsDimensionSpectralValue hfactor hdiff p.val t) :
    t=(traceFreeDimension hfactor hdiff p : ℂ) := by
  classical
  let r : AlgebraProjection M := ⟨1-p.val,p.property.one_sub⟩
  let a (b : Bool) : AlgebraProjection M := if b then r else p
  have hpr : p.val*r.val=0 := by
    change p.val*(1-p.val)=0
    rw [mul_sub,mul_one,p.property.isIdempotentElem.eq,sub_self]
  have ho (b c : Bool) (hbc : b≠c) : (a b).val*(a c).val=0 := by
    cases b <;> cases c
    · exact (hbc rfl).elim
    · exact hpr
    · exact PartialIsometry.orthogonal_reverse p r hpr
    · exact (hbc rfl).elim
  have ha : (∑ b : Bool, (a b).val)=(1 : M.toStarSubalgebra) := by
    change (∑ b : Bool, (if b then r else p).val)=1
    simp only [Fintype.sum_bool,ite_true,Bool.false_eq_true,ite_false]
    change (1-p.val)+p.val=1
    abel
  let Q : CornerPartition (⟨1,IsStarProjection.one _⟩ : AlgebraProjection M) :=
    CornerPartition.ofFamily a ho ha
  let e : Fin Q.size ≃ Bool := (Fintype.equivFin Bool).symm
  let c (i : Fin Q.size) : ℂ := if e i then 0 else 1
  have hQ (i : Fin Q.size) : Commute (Q.piece i).val p.val := by
    change Commute (a (e i)).val p.val
    cases h : e i
    · exact Commute.refl p.val
    · exact (Commute.one_left p.val).sub_left (Commute.refl p.val)
  have hs : (∑ i, c i • (Q.piece i).val)=p.val := by
    change (∑ i, (if e i then (0 : ℂ) else 1) • (a (e i)).val)=p.val
    exact (Equiv.sum_comp e (fun b : Bool => (if b then (0 : ℂ) else 1) • (a b).val)).trans
      (by simp [a])
  have hw : (∑ i, c i*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ))=
      (traceFreeDimension hfactor hdiff p : ℂ) := by
    change (∑ i, (if e i then (0 : ℂ) else 1)*
      (traceFreeDimension hfactor hdiff (a (e i)) : ℂ))=_
    exact (Equiv.sum_comp e (fun b : Bool => (if b then (0 : ℂ) else 1)*
      (traceFreeDimension hfactor hdiff (a b) : ℂ))).trans (by simp [a])
  have h := ht Q c hQ
  rw [hs,sub_self,norm_zero] at h
  exact (sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))).trans hw

theorem dimensionSpectralValue_norm_le (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    ‖dimensionSpectralValue hfactor hdiff hfinite hunit x hx‖ ≤ ‖x‖ :=
  (dimensionSpectralValue_spec hfactor hdiff hfinite hunit x hx).2.norm_le hfactor hdiff

theorem dimensionSpectralValue_projection (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (p : AlgebraProjection M) :
    dimensionSpectralValue hfactor hdiff hfinite hunit p.val p.property.isSelfAdjoint=
      (traceFreeDimension hfactor hdiff p : ℂ) :=
  (dimensionSpectralValue_spec hfactor hdiff hfinite hunit p.val p.property.isSelfAdjoint).2.on_projection
    hfactor hdiff p

theorem dimensionSpectralValue_one (hunit : (1 : M.toStarSubalgebra) ≠ 0) :
    dimensionSpectralValue hfactor hdiff hfinite hunit 1 (IsSelfAdjoint.one _)=1 := by
  rw [dimensionSpectralValue_projection hfactor hdiff hfinite hunit ⟨1,IsStarProjection.one _⟩]
  exact congrArg Complex.ofReal (traceFreeDyadicSup_self hfactor hdiff ⟨1,IsStarProjection.one _⟩)

end

/-! Finite-family tests and real homogeneity for the constructed spectral value.
These statements do not assert additivity for noncommuting operators. -/
open scoped BigOperators
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H}
variable (hfactor : ∀ c : M.toStarSubalgebra,
  (∀ a : M.toStarSubalgebra, a*c=c*a) → ∃ z : ℂ, c=z • (1 : M.toStarSubalgebra))
variable (hdiff : ∀ p : M.toStarSubalgebra, IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra, IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)
variable (hfinite : ∀ a : M.toStarSubalgebra, star a*a=1 → a*star a=1)

theorem IsDimensionSpectralValue.family_bound {x : M.toStarSubalgebra} {t : ℂ}
    (ht : IsDimensionSpectralValue hfactor hdiff x t)
    {I : Type*} [Fintype I] (q : I → AlgebraProjection M)
    (ho : ∀ i j, i≠j → (q i).val*(q j).val=0)
    (hs : ∑ i, (q i).val=(1 : M.toStarSubalgebra))
    (c : I → ℂ) (hc : ∀ i, Commute (q i).val x) :
    ‖t-∑ i, c i*(traceFreeDimension hfactor hdiff (q i) : ℂ)‖ ≤
      ‖x-∑ i, c i • (q i).val‖ := by
  classical
  let Q : CornerPartition (⟨1,IsStarProjection.one _⟩ : AlgebraProjection M) :=
    CornerPartition.ofFamily q ho hs
  let e : Fin Q.size ≃ I := (Fintype.equivFin I).symm
  have h := ht Q (fun i => c (e i)) (fun i => hc (e i))
  change ‖t-∑ i, c (e i)*(traceFreeDimension hfactor hdiff (q (e i)) : ℂ)‖ ≤
    ‖x-∑ i, c (e i) • (q (e i)).val‖ at h
  rw [Equiv.sum_comp e (fun i => c i*(traceFreeDimension hfactor hdiff (q i) : ℂ)),
    Equiv.sum_comp e (fun i => c i • (q i).val)] at h
  exact h

theorem dimensionSpectralValue_eq_of_approximants
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) (t : ℂ)
    (h : ∀ ε : ℝ, 0 < ε →
      ∃ (Q : CornerPartition (⟨1,IsStarProjection.one _⟩ : AlgebraProjection M))
        (c : Fin Q.size → ℂ),
        (∀ i, Commute (Q.piece i).val x) ∧
        ‖x-∑ i, c i • (Q.piece i).val‖ < ε ∧
        ‖t-∑ i, c i*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ)‖ < ε) :
    dimensionSpectralValue hfactor hdiff hfinite hunit x hx=t := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm ?_ (norm_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨Q,c,hc,hxerr,hterr⟩ := h (ε/2) (half_pos hε)
  have hxval := (dimensionSpectralValue_spec hfactor hdiff hfinite hunit x hx).2 Q c hc
  have htri := dist_triangle
    (dimensionSpectralValue hfactor hdiff hfinite hunit x hx)
    (∑ i, c i*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ)) t
  simp only [dist_eq_norm] at htri
  rw [norm_sub_rev (∑ i, c i*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ)) t] at htri
  linarith

theorem dimensionSpectralValue_real_smul
    (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (r : ℝ) (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    dimensionSpectralValue hfactor hdiff hfinite hunit (r • x) ((IsSelfAdjoint.all r).smul hx)=
      (r : ℂ)*dimensionSpectralValue hfactor hdiff hfinite hunit x hx := by
  apply dimensionSpectralValue_eq_of_approximants hfactor hdiff hfinite hunit
  intro ε hε
  have hr : 0 < ‖r‖+1 := by positivity
  obtain ⟨Q,c,_,hQ,herr⟩ := exists_finite_spectral_approximation_preserving_commutant
    ⟨1,IsStarProjection.one _⟩ x hx (ε/(‖r‖+1)) (div_pos hε hr)
  simp only [one_mul,mul_one] at herr
  have hc := hQ x (Commute.refl x) (Commute.one_left x)
  have hval := (dimensionSpectralValue_spec hfactor hdiff hfinite hunit x hx).2
    Q (fun i => (c i : ℂ)) hc
  have hb : ‖r‖*(ε/(‖r‖+1)) < ε := by
    have hh := (div_pos hε hr)
    have he : (‖r‖+1)*(ε/(‖r‖+1))=ε := mul_div_cancel₀ _ (ne_of_gt hr)
    nlinarith
  refine ⟨Q,fun i => (r : ℂ)*(c i : ℂ),?_,?_,?_⟩
  · intro i
    show (Q.piece i).val*(r • x)=(r • x)*(Q.piece i).val
    rw [mul_smul_comm,smul_mul_assoc,(hc i).eq]
  · have he : (r • x)-∑ i, ((r : ℂ)*(c i : ℂ)) • (Q.piece i).val=
        r • (x-∑ i, (c i : ℂ) • (Q.piece i).val) := by
      simp only [smul_sub,Finset.smul_sum,← smul_assoc,Complex.real_smul]
    rw [he,norm_smul]
    exact (mul_le_mul_of_nonneg_left herr.le (norm_nonneg r)).trans_lt hb
  · rw [show (∑ i, ((r : ℂ)*(c i : ℂ))*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ))=
        (r : ℂ)*(∑ i, (c i : ℂ)*(traceFreeDimension hfactor hdiff (Q.piece i) : ℂ)) by
          rw [Finset.mul_sum]; simp only [mul_assoc],← mul_sub,norm_mul,Complex.norm_real]
    exact (mul_le_mul_of_nonneg_left (hval.trans herr.le) (norm_nonneg r)).trans_lt hb

theorem dimensionSpectralValue_zero (hunit : (1 : M.toStarSubalgebra) ≠ 0) :
    dimensionSpectralValue hfactor hdiff hfinite hunit 0 (IsSelfAdjoint.zero _)=0 := by
  have h := dimensionSpectralValue_norm_le hfactor hdiff hfinite hunit 0 (IsSelfAdjoint.zero _)
  rw [norm_zero] at h
  exact norm_eq_zero.mp (le_antisymm h (norm_nonneg _))

theorem dimensionSpectralValue_neg (hunit : (1 : M.toStarSubalgebra) ≠ 0)
    (x : M.toStarSubalgebra) (hx : IsSelfAdjoint x) :
    dimensionSpectralValue hfactor hdiff hfinite hunit (-x) hx.neg=
      -dimensionSpectralValue hfactor hdiff hfinite hunit x hx := by
  simpa only [neg_one_smul,Complex.ofReal_neg,Complex.ofReal_one,neg_one_mul] using
    dimensionSpectralValue_real_smul hfactor hdiff hfinite hunit (-1) x hx

end Generator.Tracial

end

end OAI
