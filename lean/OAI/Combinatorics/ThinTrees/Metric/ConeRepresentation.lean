import Mathlib
import OAI.Combinatorics.ThinTrees.Continuation.CenteredDomain

namespace OAI

/-! Metric cone representation. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical MatrixOrder Matrix.Norms.Elementwise Topology
open Filter

section Representation
variable {n : ℕ} {J : Type*} [Fintype J]

def coneImage (W : J → Matrix (Fin n) (Fin n) ℝ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {A | ∃P : Matrix (Fin n) (Fin n) ℝ, ∃lam : J → ℝ,
    P.PosSemidef ∧ (∀j, 0 ≤ lam j) ∧ A=P+∑j, lam j • W j}

lemma continuous_trace : Continuous (fun P : Matrix (Fin n) (Fin n) ℝ => P.trace) := by
  simpa only [mul_one] using trace_pairing_continuous (1 : Matrix (Fin n) (Fin n) ℝ)

lemma psd_trace_compact {c : ℝ} (hc : 0 ≤ c) :
    IsCompact {P : Matrix (Fin n) (Fin n) ℝ | P.PosSemidef ∧ P.trace ≤ c} := by
  apply Metric.isCompact_iff_isClosed_bounded.mpr
  refine ⟨isClosed_psd.inter (isClosed_le continuous_trace continuous_const),?_⟩
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨c,fun P hP => ?_⟩
  have hd : ∀i, P i i ≤ c := fun i =>
    (single_le_sum (fun j _ => hP.1.diag_nonneg (i:=j)) (mem_univ i)).trans hP.2
  apply (pi_norm_le_iff_of_nonneg hc).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg hc).mpr
  intro j
  simpa only [Real.norm_eq_abs] using psd_entry_bound hP.1 hc hd i j

lemma coneImage_trace_bound (W : J → Matrix (Fin n) (Fin n) ℝ)
    (hW : ∀j, (W j).trace=2) (P : Matrix (Fin n) (Fin n) ℝ) (lam : J → ℝ)
    (hP : P.PosSemidef) (hlam : ∀j, 0 ≤ lam j) {c : ℝ}
    (ht : (P+∑j, lam j • W j).trace ≤ c) :
    P.trace ≤ c ∧ ∀j, lam j ≤ c := by
  simp only [trace_add,trace_sum,trace_smul,smul_eq_mul,hW,←sum_mul] at ht
  have hsum : 0 ≤ ∑j, lam j := sum_nonneg (fun j _ => hlam j)
  refine ⟨by linarith only [hsum,ht],?_⟩
  intro j
  have hj := single_le_sum (fun i _ => hlam i) (mem_univ j)
  have hp := hP.trace_nonneg
  linarith only [ht,hp,hlam j,hj]

lemma coneImage_closed (W : J → Matrix (Fin n) (Fin n) ℝ)
    (hW : ∀j, (W j).trace=2) : IsClosed (coneImage W) := by
  let : FirstCountableTopology (Matrix (Fin n) (Fin n) ℝ) :=
    inferInstanceAs (FirstCountableTopology (Fin n → Fin n → ℝ))
  apply IsSeqClosed.isClosed
  intro A L hA hlim
  choose P lam hP hlam he using hA
  have htr : Tendsto (fun k => (A k).trace) atTop (𝓝 L.trace) := continuous_trace.tendsto L |>.comp hlim
  obtain ⟨c,hc⟩ := (htr.cauchySeq.isBounded_range).exists_norm_le
  let d := max c 0
  have hd : 0 ≤ d := le_max_right _ _
  let K := {P : Matrix (Fin n) (Fin n) ℝ | P.PosSemidef ∧ P.trace ≤ d} ×ˢ
    Set.Icc (0 : J → ℝ) (fun _ => d)
  have hK : IsCompact K := (psd_trace_compact hd).prod isCompact_Icc
  have hw : ∀k, (P k,lam k) ∈ K := by
    intro k
    have hle : (P k+∑j, lam k j • W j).trace ≤ d := by
      rw [←he k]
      exact (le_abs_self _).trans ((hc _ (Set.mem_range_self k)).trans (le_max_left _ _))
    have hb := coneImage_trace_bound W hW (P k) (lam k) (hP k) (hlam k) hle
    exact ⟨⟨hP k,hb.1⟩,hlam k,hb.2⟩
  obtain ⟨p,hp,φ,hφ,hseq⟩ := hK.tendsto_subseq hw
  have hcont : Continuous (fun p : Matrix (Fin n) (Fin n) ℝ × (J → ℝ) =>
    p.1+∑j, p.2 j • W j) := by fun_prop
  have hi := (hcont.tendsto p).comp hseq
  have hi' : Tendsto (fun k => P (φ k)+∑j, lam (φ k) j • W j) atTop (𝓝 L) := by
    simpa only [Function.comp_def,←he] using hlim.comp hφ.tendsto_atTop
  exact ⟨p.1,p.2,hp.1.1,hp.2.1,(tendsto_nhds_unique hi' hi)⟩

lemma coneImage_zero (W : J → Matrix (Fin n) (Fin n) ℝ) : 0 ∈ coneImage W := by
  exact ⟨0,fun _ => 0,PosSemidef.zero,fun _ => le_refl _,by simp⟩

lemma coneImage_add (W : J → Matrix (Fin n) (Fin n) ℝ)
    {A B : Matrix (Fin n) (Fin n) ℝ} (hA : A ∈ coneImage W) (hB : B ∈ coneImage W) :
    A+B ∈ coneImage W := by
  obtain ⟨P,lam,hP,hlam,rfl⟩ := hA
  obtain ⟨Q,γ,hQ,hγ,rfl⟩ := hB
  refine ⟨P+Q,lam+γ,hP.add hQ,fun j => add_nonneg (hlam j) (hγ j),?_⟩
  simp only [Pi.add_apply,add_smul,sum_add_distrib]
  abel

lemma coneImage_smul (W : J → Matrix (Fin n) (Fin n) ℝ)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A ∈ coneImage W) {a : ℝ} (ha : 0 ≤ a) :
    a • A ∈ coneImage W := by
  obtain ⟨P,lam,hP,hlam,rfl⟩ := hA
  refine ⟨a • P,fun j => a*lam j,hP.smul ha,fun j => mul_nonneg ha (hlam j),?_⟩
  simp only [smul_add,smul_sum,smul_smul]

def representedCone (W : J → Matrix (Fin n) (Fin n) ℝ) (hW : ∀j, (W j).trace=2) :
    ProperCone ℝ (Matrix (Fin n) (Fin n) ℝ) where
  carrier := coneImage W
  zero_mem' := coneImage_zero W
  add_mem' := coneImage_add W
  smul_mem' := fun a _ hA => coneImage_smul W hA a.property
  isClosed' := coneImage_closed W hW

lemma psd_mem_coneImage (W : J → Matrix (Fin n) (Fin n) ℝ)
    {P : Matrix (Fin n) (Fin n) ℝ} (hP : P.PosSemidef) : P ∈ coneImage W := by
  exact ⟨P,fun _ => 0,hP,fun _ => le_refl _,by simp⟩

lemma generator_mem_coneImage (W : J → Matrix (Fin n) (Fin n) ℝ) (j : J) :
    W j ∈ coneImage W := by
  refine ⟨0,Pi.single j 1,PosSemidef.zero,?_,?_⟩
  · intro i
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  · simp [Pi.single_apply]

end Representation
section TraceDual
variable {n : ℕ}

def linearTraceMatrix (f : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ) :
    Matrix (Fin n) (Fin n) ℝ := fun i j => f (Matrix.single j i 1)

lemma linearTraceMatrix_pairing (f : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ) : (X*linearTraceMatrix f).trace=f X := by
  have hf : f X = ∑i, ∑j, X i j*f (Matrix.single i j 1) := by
    nth_rw 1 [matrix_eq_sum_single X]
    simp only [map_sum]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    rw [show Matrix.single i j (X i j)=(X i j) • Matrix.single i j (1 : ℝ) by
      simp only [smul_single,smul_eq_mul,mul_one]]
    simp only [map_smul,smul_eq_mul]
  simpa only [Matrix.trace,diag_apply,mul_apply,linearTraceMatrix] using hf.symm

lemma trace_pairing_transpose_right {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X.IsHermitian) (Z : Matrix (Fin n) (Fin n) ℝ) :
    (X*Zᵀ).trace=(X*Z).trace := by
  rw [←trace_transpose (X*Zᵀ),transpose_mul,transpose_transpose,
    (isHermitian_iff_isSymm.mp hX).eq,trace_mul_comm]

def symmetricTraceMatrix (f : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ) :
    Matrix (Fin n) (Fin n) ℝ := (1/2 : ℝ) • (linearTraceMatrix f+(linearTraceMatrix f)ᵀ)

lemma symmetricTraceMatrix_hermitian (f : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ) :
    (symmetricTraceMatrix f).IsHermitian := by
  apply isHermitian_iff_isSymm.mpr
  simp only [IsSymm,symmetricTraceMatrix,transpose_smul,transpose_add,transpose_transpose]
  rw [add_comm]

lemma symmetricTraceMatrix_pairing (f : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ)
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.IsHermitian) :
    (X*symmetricTraceMatrix f).trace=f X := by
  rw [symmetricTraceMatrix,mul_smul_comm,mul_add,trace_smul,trace_add,
    trace_pairing_transpose_right hX,linearTraceMatrix_pairing]
  simp only [smul_eq_mul]
  ring

lemma symmetricTraceMatrix_psd (f : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ)
    (hf : ∀ P : Matrix (Fin n) (Fin n) ℝ, P.PosSemidef → 0 ≤ f P) :
    (symmetricTraceMatrix f).PosSemidef := by
  apply PosSemidef.of_dotProduct_mulVec_nonneg (symmetricTraceMatrix_hermitian f)
  intro x
  simpa only [star_trivial,←ShortcutDual.trace_outer_mul,
    symmetricTraceMatrix_pairing f (ShortcutDual.outer_posSemidef x).isHermitian]
    using hf (vecMulVec x x) (ShortcutDual.outer_posSemidef x)

abbrev DistinctTriple (n : ℕ) :=
  {ijk : Fin n × Fin n × Fin n // ijk.1 ≠ ijk.2.1 ∧ ijk.2.1 ≠ ijk.2.2 ∧ ijk.1 ≠ ijk.2.2}

def triangleMatrix (u v w : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  vecMulVec (difference u v) (difference u v)+
  vecMulVec (difference v w) (difference v w)-
  vecMulVec (difference u w) (difference u w)

def triangleGenerator (ijk : DistinctTriple n) : Matrix (Fin n) (Fin n) ℝ :=
  triangleMatrix ijk.1.1 ijk.1.2.1 ijk.1.2.2

lemma triangleMatrix_hermitian (u v w : Fin n) : (triangleMatrix u v w).IsHermitian :=
  ((ShortcutDual.outer_posSemidef _).isHermitian.add
    (ShortcutDual.outer_posSemidef _).isHermitian).sub (ShortcutDual.outer_posSemidef _).isHermitian

lemma difference_norm_sq {u v : Fin n} (huv : u ≠ v) :
    difference u v ⬝ᵥ difference u v=2 := by
  norm_num [difference,point,sub_dotProduct,dotProduct_sub,huv,huv.symm]

lemma triangleGenerator_trace (ijk : DistinctTriple n) : (triangleGenerator ijk).trace=2 := by
  simp only [triangleGenerator,triangleMatrix,trace_sub,trace_add,trace_vecMulVec,
    difference_norm_sq ijk.property.1,difference_norm_sq ijk.property.2.1,
    difference_norm_sq ijk.property.2.2]
  norm_num

lemma triangleMatrix_ones (u v w : Fin n) : triangleMatrix u v w *ᵥ ones n=0 := by
  have h (a b : Fin n) : vecMulVec (difference a b) (difference a b) *ᵥ ones n=0 := by
    rw [vecMulVec_mulVec,dotProduct_comm,ones_dot,difference_sum,MulOpposite.op_zero,zero_smul]
  simp only [triangleMatrix,sub_mulVec,add_mulVec,h,zero_add,sub_zero]

lemma triangleMatrix_pairing (u v w : Fin n) (Z : Matrix (Fin n) (Fin n) ℝ) :
    (triangleMatrix u v w*Z).trace=
      qform Z (difference u v)+qform Z (difference v w)-qform Z (difference u w) := by
  simp only [triangleMatrix,sub_mul,add_mul,trace_add,trace_sub,ShortcutDual.trace_outer_mul,qform]

lemma test_iff_generators (Z : Matrix (Fin n) (Fin n) ℝ) :
    Test Z ↔ Z.PosSemidef ∧ ∀ijk : DistinctTriple n, 0 ≤ (triangleGenerator ijk*Z).trace := by
  refine ⟨fun hZ => ⟨hZ.1,fun ijk => ?_⟩,fun hZ => ⟨hZ.1,fun u v w => ?_⟩⟩
  · simpa only [triangleGenerator,triangleMatrix_pairing,sub_nonneg] using hZ.2 _ _ _
  · by_cases huv : u=v
    · subst v
      simp [difference,qform]
    by_cases hvw : v=w
    · subst w
      simp [difference,qform]
    by_cases huw : u=w
    · subst w
      simpa only [difference,sub_self,mulVec_zero,dotProduct_zero,qform]
        using add_nonneg (qform_nonneg hZ.1 (difference u v)) (qform_nonneg hZ.1 (difference v u))
    have hh := hZ.2 ⟨(u,v,w),huv,hvw,huw⟩
    simpa only [triangleGenerator,triangleMatrix_pairing,sub_nonneg] using hh

theorem metric_dual_representation {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) :
    (∀Z, Test Z → 0 ≤ (A*Z).trace) ↔ A ∈ coneImage (triangleGenerator (n:=n)) := by
  constructor
  · intro hdual
    by_contra hn
    let : LocallyConvexSpace ℝ (Matrix (Fin n) (Fin n) ℝ) :=
      inferInstanceAs (LocallyConvexSpace ℝ (Fin n → Fin n → ℝ))
    obtain ⟨f,hf,hfA⟩ := (representedCone triangleGenerator triangleGenerator_trace).hyperplane_separation_point hn
    have hfP : ∀P : Matrix (Fin n) (Fin n) ℝ, P.PosSemidef → 0 ≤ f P :=
      fun P hP => hf P (psd_mem_coneImage triangleGenerator hP)
    let Z := symmetricTraceMatrix f.toLinearMap
    have hZ : Test Z := by
      apply (test_iff_generators Z).mpr
      refine ⟨symmetricTraceMatrix_psd f.toLinearMap hfP,fun ijk => ?_⟩
      change 0 ≤ (triangleGenerator ijk*symmetricTraceMatrix f.toLinearMap).trace
      have hi : (triangleGenerator ijk).IsHermitian := triangleMatrix_hermitian _ _ _
      rw [symmetricTraceMatrix_pairing f.toLinearMap hi]
      exact hf _ (generator_mem_coneImage triangleGenerator ijk)
    have hz := hdual Z hZ
    rw [symmetricTraceMatrix_pairing f.toLinearMap hA] at hz
    exact (not_lt_of_ge hz) hfA
  · rintro ⟨P,lam,hP,hlam,rfl⟩ Z hZ
    simp only [add_mul,sum_mul,smul_mul_assoc,trace_add,trace_sum,trace_smul,smul_eq_mul]
    exact add_nonneg (trace_pairing_nonneg hP hZ.1)
      (sum_nonneg fun ijk _ => mul_nonneg (hlam ijk) (((test_iff_generators Z).mp hZ).2 ijk))

lemma trace_centered_right {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (hA0 : A *ᵥ ones n=0) (Z : Matrix (Fin n) (Fin n) ℝ) :
    (A*centered Z).trace=(A*Z).trace := by
  calc
    (A*centered Z).trace=((A*centering n)*Z*centering n).trace := by
      simp only [centered,mul_assoc]
    _ = (A*Z*centering n).trace := by rw [mul_centering_of_ones hA0]
    _ = (centering n*(A*Z)).trace := trace_mul_comm _ _
    _ = (A*Z).trace := by rw [←mul_assoc,centering_mul_of_ones hA hA0]

theorem centered_metric_dual_representation (hn : 0 < n)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (hA0 : A *ᵥ ones n=0) :
    (∀Z, CenteredTest Z → 0 ≤ (A*Z).trace) ↔
      ∃P : Matrix (Fin n) (Fin n) ℝ, ∃lam : DistinctTriple n → ℝ,
        P.PosSemidef ∧ P *ᵥ ones n=0 ∧ (∀ijk, 0 ≤ lam ijk) ∧
          A=P+∑ijk, lam ijk • triangleGenerator ijk := by
  constructor
  · intro hdual
    have hd : ∀Z, Test Z → 0 ≤ (A*Z).trace := fun Z hZ => by
      have h := hdual _ (test_centered hn hZ)
      rwa [trace_centered_right hA hA0] at h
    obtain ⟨P,lam,hP,hlam,he⟩ := (metric_dual_representation hA).mp hd
    refine ⟨P,lam,hP,?_,hlam,he⟩
    rw [he,add_mulVec] at hA0
    simpa only [sum_mulVec,smul_mulVec,triangleGenerator,triangleMatrix_ones,
      smul_zero,sum_const_zero,add_zero] using hA0
  · rintro ⟨P,lam,hP,_,hlam,he⟩ Z hZ
    exact (metric_dual_representation hA).mpr ⟨P,lam,hP,hlam,he⟩ Z hZ.1

theorem metricDomain_iff_lmi {m : ℕ} (G : MultiGraph n m) (hn : 0 < n)
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.IsHermitian) (hX0 : X *ᵥ ones n=0) :
    X ∈ metricDomain G ↔ G.laplacian univ ≤ X ∧
      ∃lam : DistinctTriple n → ℝ, (∀ijk, 0 ≤ lam ijk) ∧
        ((3:ℝ) • G.laplacian univ-X-∑ijk, lam ijk • triangleGenerator ijk).PosSemidef := by
  have hA : ((3:ℝ) • G.laplacian univ-X).IsHermitian :=
    ((G.laplacian_psd univ).smul (by norm_num : (0:ℝ) ≤ 3)).isHermitian.sub hX
  have hA0 : ((3:ℝ) • G.laplacian univ-X) *ᵥ ones n=0 := by
    simp only [sub_mulVec,smul_mulVec,laplacian_ones,hX0,smul_zero,sub_self]
  constructor
  · intro h
    refine ⟨h.2.2.1,?_⟩
    obtain ⟨P,lam,hP,_,hlam,he⟩ := (centered_metric_dual_representation hn hA hA0).mp
      (fun Z hZ => by
        simpa only [sub_mul,smul_mul_assoc,trace_sub,trace_smul,smul_eq_mul,sub_nonneg]
          using h.2.2.2 Z hZ)
    refine ⟨lam,hlam,?_⟩
    rwa [he,add_sub_cancel_right]
  · rintro ⟨hLX,lam,hlam,hP⟩
    refine ⟨hX,hX0,hLX,fun Z hZ => ?_⟩
    have h := (metric_dual_representation hA).mpr
      ⟨_,lam,hP,hlam,by abel⟩ Z hZ.1
    simpa only [sub_mul,smul_mul_assoc,trace_sub,trace_smul,smul_eq_mul,sub_nonneg] using h

lemma laplacian_trace {m : ℕ} (G : MultiGraph n m) : (G.laplacian univ).trace=2*m := by
  simp only [laplacian,trace_sum,trace_vecMulVec]
  have he (e : Fin m) : G.incidence e ⬝ᵥ G.incidence e=2 := difference_norm_sq (G.loopless e)
  simp only [he,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

lemma domain_trace_size {m : ℕ} (G : MultiGraph n m) (hn : 0 < n)
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : X ∈ metricDomain G) : X.trace ≤ 6*m := by
  have h := domain_trace_bound G hn hX
  rw [laplacian_trace G] at h
  linarith only [h]

lemma domain_multiplier_bound {m : ℕ} (G : MultiGraph n m)
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.PosSemidef)
    (lam : DistinctTriple n → ℝ)
    (hP : ((3:ℝ) • G.laplacian univ-X-∑ijk, lam ijk • triangleGenerator ijk).PosSemidef) :
    (∑ijk, lam ijk) ≤ 3*m := by
  have h := hP.trace_nonneg
  simp only [trace_sub,trace_smul,smul_eq_mul,trace_sum,triangleGenerator_trace,←sum_mul,
    laplacian_trace G] at h
  linarith only [h,hX.trace_nonneg]

end TraceDual

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
