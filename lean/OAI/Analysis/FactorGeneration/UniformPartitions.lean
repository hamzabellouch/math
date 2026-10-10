import Mathlib.Algebra.Order.Floor.Semiring
import OAI.Analysis.FactorGeneration.SpectralApproximation

namespace OAI

noncomputable section

namespace Generator.Tracial

/-! Finite equal-trace partitions in an actual diffuse algebra, constructed
by repeated exact trace cuts. No matrix units or comparison theorem are
assumed. These partitions do not yet approximate an arbitrary given
spectral partition. -/
section
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)
variable (hdiff : ∀ p : M.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)

include hdiff in
theorem exists_uniform_trace_partition (n : ℕ) (p : AlgebraProjection M)
    (r : ℝ) (hr : 0 ≤ r) (ht : τ.trace p.val=((n : ℝ)*r : ℂ)) :
    ∃ Q : CornerPartition p,Q.size=n ∧ ∀ i,τ.trace (Q.piece i).val=(r : ℂ) := by
  induction n generalizing p with
  | zero =>
    have hp0 : p.val=0 := by
      by_contra h
      have hpos := projection_trace_pos τ p.val p.property h
      simp only [Nat.cast_zero,zero_mul,Complex.ofReal_zero] at ht
      rw [ht,Complex.zero_re] at hpos
      exact (lt_irrefl 0 hpos)
    refine ⟨⟨0,Fin.elim0,fun i => Fin.elim0 i,?_⟩,rfl,fun i => Fin.elim0 i⟩
    simpa only [Finset.univ_eq_empty,Finset.sum_empty] using hp0.symm
  | succ n ih =>
    have hrp : r ≤ (τ.trace p.val).re := by
      have htR := congrArg Complex.re ht
      simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
        mul_zero,sub_zero,Nat.cast_succ] at htR
      rw [htR]
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
    obtain ⟨q,hq,hpq,hqp,hqt⟩ :=
      exists_exact_trace_subprojection τ hdiff p.val p.property r hr hrp
    let s : AlgebraProjection M := ⟨p.val-q,hq.sub_of_mul_eq_right p.property hpq⟩
    have hst : τ.trace s.val=((n : ℝ)*r : ℂ) := by
      change τ.trace (p.val-q)=_
      rw [trace_sub,ht,hqt]
      push_cast
      ring
    obtain ⟨Q,hsize,hQ⟩ := ih s hst
    have hleft (i : Fin Q.size) : q*(Q.piece i).val=0 := by
      have hle : (p.val-q)*(Q.piece i).val=(Q.piece i).val := Q.piece_le i
      calc q*(Q.piece i).val = q*((p.val-q)*(Q.piece i).val) := by rw [hle]
        _ = 0 := by rw [← mul_assoc,mul_sub,hqp,hq.isIdempotentElem.eq,sub_self,zero_mul]
    have hright (i : Fin Q.size) : (Q.piece i).val*q=0 := by
      simpa only [star_mul,hq.isSelfAdjoint.star_eq,
        (Q.piece i).property.isSelfAdjoint.star_eq,star_zero] using congrArg star (hleft i)
    let a : Fin (Q.size+1) → AlgebraProjection M := Fin.cons ⟨q,hq⟩ Q.piece
    have ha (i j : Fin (Q.size+1)) (hij : i ≠ j) : (a i).val*(a j).val=0 := by
      revert hij
      refine Fin.cases ?_ (fun i => ?_) i
      · refine Fin.cases ?_ (fun j => ?_) j
        · intro hij
          exact (hij rfl).elim
        · intro _
          exact hleft j
      · refine Fin.cases ?_ (fun j => ?_) j
        · intro _
          exact hright i
        · intro hij
          exact Q.orthogonal i j (fun h => hij (congrArg Fin.succ h))
    have hat : (∑ i,(a i).val)=p.val := by
      rw [Fin.sum_univ_succ]
      change q+(∑ i,(Q.piece i).val)=p.val
      rw [Q.total]
      change q+(p.val-q)=p.val
      abel
    let R : CornerPartition p := ⟨Q.size+1,a,ha,hat⟩
    refine ⟨R,congrArg (fun k => k+1) hsize,?_⟩
    intro i
    exact Fin.cases hqt hQ i

/-! Complete finitely many orthogonal grid-trace projections to an actual
equal-trace unit partition, retaining explicit disjoint groups of pieces. -/

include hdiff in
theorem exists_uniform_trace_extension {ι : Type*} [Fintype ι]
    (q : ι → AlgebraProjection M)
    (hq : ∀ i j,i ≠ j → (q i).val*(q j).val=0)
    (n : ℕ) (hn : 0 < n) (m : ι → ℕ) (hm : ∑ i,m i ≤ n)
    (ht : ∀ i,τ.trace (q i).val=(((m i : ℝ)*(n : ℝ)⁻¹ : ℝ) : ℂ)) :
    ∃ R : CornerPartition (identityProjection M), R.size=n ∧
      (∀ j,τ.trace (R.piece j).val=(((n : ℝ)⁻¹ : ℝ) : ℂ)) ∧
      ∃ J : ι → Finset (Fin R.size),
        (∀ i j,i ≠ j → Disjoint (J i) (J j)) ∧
        ∀ i,(∑ j ∈ J i,(R.piece j).val)=(q i).val := by
  classical
  have hnR : (n : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hn)
  obtain ⟨C,e,he,hrem⟩ := exists_completed_orthogonal_family q hq
  let count : Option ι → ℕ := fun a => a.elim (n-∑ i,m i) m
  have hsum : τ.trace (∑ i,(q i).val)=
      ((((∑ i,m i : ℕ) : ℝ)*(n : ℝ)⁻¹ : ℝ) : ℂ) := by
    change coordinateTraceLinear τ (∑ i,(q i).val)=_
    rw [map_sum]
    change (∑ i,τ.trace (q i).val)=_
    simp only [ht]
    push_cast
    rw [Finset.sum_mul]
  have hc (a : Option ι) : τ.trace (C.piece (e a)).val=
      (((count a : ℝ)*(n : ℝ)⁻¹ : ℝ) : ℂ) := by
    cases a with
    | some i => simpa only [he,count,Option.elim_some] using ht i
    | none =>
      rw [hrem,trace_sub,τ.trace_one,hsum]
      dsimp [count]
      rw [Nat.cast_sub hm]
      push_cast
      have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hnR
      field_simp
  have hC (j : Fin C.size) : τ.trace (C.piece j).val=
      (((count (e.symm j) : ℝ)*(n : ℝ)⁻¹ : ℝ) : ℂ) := by
    simpa only [Equiv.apply_symm_apply] using hc (e.symm j)
  choose D hDsize hDt using fun j => exists_uniform_trace_partition τ hdiff
    (count (e.symm j)) (C.piece j) (n : ℝ)⁻¹ (by positivity) (by simpa only [Complex.ofReal_mul] using hC j)
  let R := C.refineBlocks D
  have hRt (j : Fin R.size) : τ.trace (R.piece j).val=(((n : ℝ)⁻¹ : ℝ) : ℂ) := by
    exact hDt _ _
  have hsize : R.size=n := by
    have htotal := R.trace_total τ
    have heq : (R.size : ℝ)*(n : ℝ)⁻¹=1 := by
      simpa only [hRt,Complex.ofReal_re,Finset.sum_const,Finset.card_univ,
        Fintype.card_fin,nsmul_eq_mul,identityProjection,τ.trace_one,Complex.one_re] using htotal
    have hmul := mul_inv_cancel₀ hnR
    have hreal : (R.size : ℝ)=(n : ℝ) :=
      (mul_right_cancel₀ (inv_ne_zero hnR)) (heq.trans hmul.symm)
    exact_mod_cast hreal
  refine ⟨R,hsize,hRt,fun i => C.blockIndices D (e (some i)),?_,?_⟩
  · intro i j hij
    apply C.blockIndices_disjoint
    intro h
    exact hij (Option.some.inj (e.injective h))
  · intro i
    exact (C.sum_blockIndices D (e (some i))).trans (congrArg Subtype.val (he i))

/-! Quantitative equal-trace approximation by rounding down spectral pieces.
All projections and partitions are constructed in the given diffuse algebra. -/

include hdiff in
theorem exists_rounded_trace_subprojection (p : AlgebraProjection M)
    (n : ℕ) (hn : 0 < n) :
    ∃ m : ℕ, ∃ q : AlgebraProjection M, q ≤ p ∧
      τ.trace q.val=(((m : ℝ)*(n : ℝ)⁻¹ : ℝ) : ℂ) ∧
      τ.norm₂ (p.val-q.val)^2 < (n : ℝ)⁻¹ := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  let t := (τ.trace p.val).re
  have ht : 0 ≤ t := by
    dsimp [t]
    rw [projection_trace_sq τ p.val p.property]
    positivity
  let m := ⌊t*(n : ℝ)⌋₊
  have hlow : (m : ℝ)*(n : ℝ)⁻¹ ≤ t := by
    apply (mul_le_mul_iff_left₀ hnR).mp
    have h := Nat.floor_le (mul_nonneg ht hnR.le)
    dsimp [m]
    field_simp
    nlinarith
  have herror : t-(m : ℝ)*(n : ℝ)⁻¹ < (n : ℝ)⁻¹ := by
    have h := Nat.lt_floor_add_one (t*(n : ℝ))
    apply (mul_lt_mul_iff_left₀ hnR).mp
    dsimp [m]
    field_simp
    nlinarith
  obtain ⟨q,hq,hpq,_,hqt⟩ := exists_exact_trace_subprojection τ hdiff p.val p.property
    ((m : ℝ)*(n : ℝ)⁻¹) (by positivity) hlow
  refine ⟨m,⟨q,hq⟩,hpq,hqt,?_⟩
  rw [← projection_trace_sq τ _ (hq.sub_of_mul_eq_right p.property hpq),
    trace_sub,hqt,Complex.sub_re,Complex.ofReal_re]
  exact herror

include hdiff in
theorem exists_uniform_trace_approximation
    (Q : CornerPartition (identityProjection M)) (n : ℕ) (hn : 0 < n) :
    ∃ R : CornerPartition (identityProjection M), R.size=n ∧
      (∀ j,τ.trace (R.piece j).val=(((n : ℝ)⁻¹ : ℝ) : ℂ)) ∧
      ∃ J : Fin Q.size → Finset (Fin R.size),
        (∀ i j,i ≠ j → Disjoint (J i) (J j)) ∧
        (∀ i,(Q.piece i).val*(∑ j ∈ J i,(R.piece j).val)=
          ∑ j ∈ J i,(R.piece j).val) ∧
        ∀ i,τ.norm₂ ((Q.piece i).val-∑ j ∈ J i,(R.piece j).val)^2 < (n : ℝ)⁻¹ := by
  classical
  choose m q hle ht herr using fun i => exists_rounded_trace_subprojection τ hdiff (Q.piece i) n hn
  have horth (i j : Fin Q.size) (hij : i ≠ j) : (q i).val*(q j).val=0 :=
    orthogonal_subprojections (Q.orthogonal i j hij) (hle i) (hle j)
  have htracele (i : Fin Q.size) : (m i : ℝ)*(n : ℝ)⁻¹ ≤ (τ.trace (Q.piece i).val).re := by
    have hpos : 0 ≤ (τ.trace ((Q.piece i).val-(q i).val)).re := by
      rw [projection_trace_sq τ _ ((q i).property.sub_of_mul_eq_right (Q.piece i).property (hle i))]
      positivity
    rw [trace_sub,ht,Complex.sub_re,Complex.ofReal_re] at hpos
    linarith
  have hsum : (∑ i,m i : ℕ) ≤ n := by
    have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => htracele i)
    rw [Q.trace_total τ] at h
    have hreal : ((∑ i,m i : ℕ) : ℝ)*(n : ℝ)⁻¹ ≤ 1 := by
      simpa only [Nat.cast_sum,Finset.sum_mul,identityProjection,τ.trace_one,Complex.one_re] using h
    have hnR : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
    have hmul := mul_inv_cancel₀ (ne_of_gt hnR)
    have hbound : ((∑ i,m i : ℕ) : ℝ) ≤ (n : ℝ) :=
      (mul_le_mul_iff_left₀ (inv_pos.mpr hnR)).mp (hreal.trans_eq hmul.symm)
    exact_mod_cast hbound
  obtain ⟨R,hsize,hRt,J,hJdis,hJsum⟩ := exists_uniform_trace_extension τ hdiff q horth n hn m hsum ht
  refine ⟨R,hsize,hRt,J,hJdis,?_,?_⟩
  · intro i
    rw [hJsum]
    exact hle i
  · intro i
    rw [hJsum]
    exact herr i

include hdiff in
theorem exists_dyadic_trace_approximation
    (Q : CornerPartition (identityProjection M)) (ε : ℝ) (hε : 0 < ε) :
    ∃ k : ℕ, ∃ R : CornerPartition (identityProjection M), R.size=2^k ∧
      (∀ j,τ.trace (R.piece j).val=((((2^k : ℕ) : ℝ)⁻¹ : ℝ) : ℂ)) ∧
      ∃ J : Fin Q.size → Finset (Fin R.size),
        (∀ i j,i ≠ j → Disjoint (J i) (J j)) ∧
        (∀ i,(Q.piece i).val*(∑ j ∈ J i,(R.piece j).val)=
          ∑ j ∈ J i,(R.piece j).val) ∧
        ∀ i,τ.norm₂ ((Q.piece i).val-∑ j ∈ J i,(R.piece j).val)^2 < ε := by
  obtain ⟨k,hk⟩ := exists_pow_lt_of_lt_one hε (by norm_num : (2 : ℝ)⁻¹ < 1)
  have hk' : (((2^k : ℕ) : ℝ)⁻¹ : ℝ) < ε := by
    simpa only [Nat.cast_pow,Nat.cast_ofNat,inv_pow] using hk
  obtain ⟨R,hsize,ht,J,hd,hle,herr⟩ := exists_uniform_trace_approximation τ hdiff Q (2^k) (by positivity)
  exact ⟨k,R,hsize,ht,J,hd,hle,fun i => (herr i).trans hk'⟩

end

/-! A finite commuting self-adjoint family admits simultaneous L2 spectral
approximation on one constructed dyadic equal-trace partition. -/
open scoped BigOperators
open UltrapowerBridge
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {M : VonNeumannAlgebra H} (τ : TracialRepresentation M)

theorem norm₂_finset_sum_le {ι : Type*} (F : Finset ι) (x : ι → M.toStarSubalgebra) :
    τ.norm₂ (∑ i ∈ F,x i) ≤ ∑ i ∈ F,τ.norm₂ (x i) := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | @insert i F hi ih =>
    rw [Finset.sum_insert hi,Finset.sum_insert hi]
    exact (τ.norm₂_add_le _ _).trans (add_le_add le_rfl ih)

variable (hdiff : ∀ p : M.toStarSubalgebra,IsStarProjection p → p ≠ 0 →
  ∃ q : M.toStarSubalgebra,IsStarProjection q ∧ q ≠ 0 ∧ q ≠ p ∧ p*q=q ∧ q*p=q)

include hdiff in
theorem exists_dyadic_spectral_sum_approximation {ι : Type*} [Fintype ι]
    (Q : CornerPartition (identityProjection M)) (c : ι → Fin Q.size → ℂ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ k : ℕ, ∃ R : CornerPartition (identityProjection M), R.size=2^k ∧
      (∀ j,τ.trace (R.piece j).val=((((2^k : ℕ) : ℝ)⁻¹ : ℝ) : ℂ)) ∧
      ∃ d : ι → Fin R.size → ℂ, ∀ i,
        τ.norm₂ ((∑ l,c i l • (Q.piece l).val)-∑ j,d i j • (R.piece j).val) < ε := by
  classical
  let A : ℝ := ∑ i,∑ l,‖c i l‖
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let δ := ε/(A+1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hsmall : A*δ < ε := by
    dsimp [δ]
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ (by positivity : 0 < A+1)).mpr
    nlinarith
  obtain ⟨k,R,hsize,ht,J,_,_,herr⟩ := exists_dyadic_trace_approximation τ hdiff Q (δ^2) (sq_pos_of_pos hδ)
  let d : ι → Fin R.size → ℂ := fun i j => ∑ l,if j ∈ J l then c i l else 0
  have hd (i : ι) : (∑ j,d i j • (R.piece j).val)=
      ∑ l,c i l • (∑ j ∈ J l,(R.piece j).val) := by
    simp only [d,Finset.sum_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l _
    rw [Finset.smul_sum]
    simp only [ite_smul,zero_smul]
    simp
  have herr' (l : Fin Q.size) :
      τ.norm₂ ((Q.piece l).val-∑ j ∈ J l,(R.piece j).val) ≤ δ := by
    have h := herr l
    have hnonneg : 0 ≤ τ.norm₂ ((Q.piece l).val-∑ j ∈ J l,(R.piece j).val) := norm_nonneg _
    nlinarith
  refine ⟨k,R,hsize,ht,d,?_⟩
  intro i
  rw [hd,← Finset.sum_sub_distrib]
  simp only [← smul_sub]
  calc
    τ.norm₂ (∑ l,c i l • ((Q.piece l).val-∑ j ∈ J l,(R.piece j).val)) ≤
        ∑ l,τ.norm₂ (c i l • ((Q.piece l).val-∑ j ∈ J l,(R.piece j).val)) :=
      norm₂_finset_sum_le τ Finset.univ _
    _ ≤ ∑ l,‖c i l‖*δ := by
      apply Finset.sum_le_sum
      intro l _
      rw [τ.norm₂_smul]
      exact mul_le_mul_of_nonneg_left (herr' l) (norm_nonneg _)
    _ = (∑ l,‖c i l‖)*δ := (Finset.sum_mul _ _ _).symm
    _ ≤ A*δ := by
      apply mul_le_mul_of_nonneg_right _ hδ.le
      exact Finset.single_le_sum (fun j _ => Finset.sum_nonneg (fun l _ => norm_nonneg _)) (Finset.mem_univ i)
    _ < ε := hsmall

include hdiff in
theorem exists_finite_uniform_spectral_approximation {ι : Type*} [Fintype ι]
    (x : ι → M.toStarSubalgebra) (hx : ∀ i,IsSelfAdjoint (x i))
    (hcomm : ∀ i j,Commute (x i) (x j)) (ε : ℝ) (hε : 0 < ε) :
    ∃ k : ℕ, ∃ R : CornerPartition (identityProjection M), R.size=2^k ∧
      (∀ j,τ.trace (R.piece j).val=((((2^k : ℕ) : ℝ)⁻¹ : ℝ) : ℂ)) ∧
      ∃ d : ι → Fin R.size → ℂ, ∀ i,
        τ.norm₂ (x i-∑ j,d i j • (R.piece j).val) < ε := by
  classical
  obtain ⟨Q,_,_,hQ⟩ := exists_finite_abelian_spectral_refinement x hx hcomm
    (CornerPartition.single (identityProjection M))
    (by intro y _ j; exact Commute.one_left y) Finset.univ (ε/2) (by positivity)
  choose c hc using fun i => hQ i (Finset.mem_univ i)
  obtain ⟨k,R,hsize,ht,d,hd⟩ := exists_dyadic_spectral_sum_approximation τ hdiff Q c (ε/2) (by positivity)
  refine ⟨k,R,hsize,ht,d,?_⟩
  intro i
  have hsum : x i-∑ j,d i j • (R.piece j).val =
      (x i-∑ l,c i l • (Q.piece l).val)+
      ((∑ l,c i l • (Q.piece l).val)-∑ j,d i j • (R.piece j).val) := by abel
  rw [hsum]
  exact (τ.norm₂_add_le _ _).trans_lt (by
    have h₁ := (τ.norm₂_le_norm _).trans_lt (hc i)
    have h₂ := hd i
    linarith)

end Generator.Tracial

end

end OAI
