import OAI.Analysis.KadisonKastler.MatrixCommutantDistance

namespace OAI

/-! # Self-adjoint approximation by the algebra and its commutant -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def algebraCommutantSum (M : VonNeumannAlgebra H) : Set (H →L[ℂ] H) :=
  {T | ∃ a b : H →L[ℂ] H, a ∈ M ∧ b ∈ M.commutant ∧ T = a + b}

def selfAdjointAlgebraCommutantSum (M : VonNeumannAlgebra H) : Set (H →L[ℂ] H) :=
  {T | ∃ a b : H →L[ℂ] H, a ∈ M ∧ b ∈ M.commutant ∧
    IsSelfAdjoint a ∧ IsSelfAdjoint b ∧ T = a + b}

theorem selfAdjointAlgebraCommutantSum_subset (M : VonNeumannAlgebra H) :
    selfAdjointAlgebraCommutantSum M ⊆ algebraCommutantSum M := by
  rintro T ⟨a, b, ha, hb, _, _, hab⟩
  exact ⟨a, b, ha, hb, hab⟩

theorem selfAdjointAlgebraCommutantSum_zero (M : VonNeumannAlgebra H) :
    0 ∈ selfAdjointAlgebraCommutantSum M :=
  ⟨0, 0, M.zero_mem, M.commutant.zero_mem, IsSelfAdjoint.zero _, IsSelfAdjoint.zero _,
    (zero_add 0).symm⟩

theorem selfAdjointAlgebraCommutantSum_add (M : VonNeumannAlgebra H)
    {s t : H →L[ℂ] H} (hs : s ∈ selfAdjointAlgebraCommutantSum M)
    (ht : t ∈ selfAdjointAlgebraCommutantSum M) :
    s + t ∈ selfAdjointAlgebraCommutantSum M := by
  obtain ⟨a, b, ha, hb, hsa, hsb, rfl⟩ := hs
  obtain ⟨c, d, hc, hd, hsc, hsd, rfl⟩ := ht
  exact ⟨a + c, b + d, M.add_mem ha hc, M.commutant.add_mem hb hd,
    hsa.add hsc, hsb.add hsd, by abel⟩

theorem selfAdjointAlgebraCommutantSum_smul (M : VonNeumannAlgebra H)
    (r : ℝ) {s : H →L[ℂ] H} (hs : s ∈ selfAdjointAlgebraCommutantSum M) :
    r • s ∈ selfAdjointAlgebraCommutantSum M := by
  obtain ⟨a, b, ha, hb, hsa, hsb, rfl⟩ := hs
  refine ⟨r • a, r • b, ?_, ?_, (show IsSelfAdjoint r from rfl).smul hsa,
    (show IsSelfAdjoint r from rfl).smul hsb, smul_add r a b⟩
  · rw [← Complex.coe_smul]
    exact M.smul_mem ha _
  · rw [← Complex.coe_smul]
    exact M.commutant.smul_mem hb _

theorem realPart_mem_vonNeumann (M : VonNeumannAlgebra H) {a : H →L[ℂ] H} (ha : a ∈ M) :
    (realPart a : H →L[ℂ] H) ∈ M := by
  rw [realPart_apply_coe, ← Complex.coe_smul]
  exact M.smul_mem (M.add_mem ha (star_mem (s := M.toStarSubalgebra) ha)) _

theorem exists_selfAdjoint_sum_approximation
    (M : VonNeumannAlgebra H) (T : H →L[ℂ] H) (hT : IsSelfAdjoint T)
    (a b : H →L[ℂ] H) (ha : a ∈ M) (hb : b ∈ M.commutant) :
    ∃ s ∈ selfAdjointAlgebraCommutantSum M, ‖T - s‖ ≤ ‖T - (a + b)‖ := by
  let ra : H →L[ℂ] H := realPart a
  let rb : H →L[ℂ] H := realPart b
  refine ⟨ra + rb, ⟨ra, rb, realPart_mem_vonNeumann M ha,
    realPart_mem_vonNeumann M.commutant hb, (realPart a).property,
    (realPart b).property, rfl⟩, ?_⟩
  have he : T - (ra + rb) = (realPart (T - (a + b)) : H →L[ℂ] H) := by
    rw [map_sub, map_add]
    change T - (ra + rb) = (realPart T : H →L[ℂ] H) - (ra + rb)
    rw [hT.coe_realPart]
  rw [he]
  exact realPart.norm_le (T - (a + b))

theorem selfAdjoint_of_mem_algebraCommutantSum (M : VonNeumannAlgebra H)
    {s : H →L[ℂ] H} (hs : s ∈ selfAdjointAlgebraCommutantSum M) : IsSelfAdjoint s := by
  obtain ⟨a, b, _, _, ha, hb, rfl⟩ := hs
  exact ha.add hb

theorem commutator_mem_of_mem_algebraCommutantSum (M : VonNeumannAlgebra H)
    {s : H →L[ℂ] H} (hs : s ∈ selfAdjointAlgebraCommutantSum M)
    {x : H →L[ℂ] H} (hx : x ∈ M) : s * x - x * s ∈ M := by
  obtain ⟨a, b, ha, hb, _, _, rfl⟩ := hs
  have hcomm := VonNeumannAlgebra.mem_commutant_iff.mp hb x hx
  have he : (a + b) * x - x * (a + b) = a * x - x * a := by
    rw [add_mul, mul_add, ← hcomm]
    abel
  rw [he]
  exact M.sub_mem (M.mul_mem ha hx) (M.mul_mem hx ha)

end

end KadisonKastler

end OAI
