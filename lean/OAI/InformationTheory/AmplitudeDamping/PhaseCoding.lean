import OAI.InformationTheory.AmplitudeDamping.FinitePacking

namespace OAI

noncomputable section

universe u_1

section
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

def signUnitary (s : Fin 2) : Matrix.unitaryGroup (Fin 2) ℂ :=
  ⟨Matrix.diagonal (fun b ↦ if b=0 ∨ s=0 then 1 else -1), by
    constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;> fin_cases s <;>
      simp [Matrix.mul_apply,Fin.sum_univ_two,Matrix.star_apply]⟩

theorem phaseOutput_conjugate (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {p : ℝ} (hp : p ∈ Set.Icc (0:ℝ) 1) (s : Fin 2) :
    phaseOutput γ ν p s=Unitary.conjStarAlgAut ℂ _ (signUnitary s) (phaseOutput γ ν p 0) := by
  rw [phaseOutput_formula γ ν hγ hν hp s,phaseOutput_formula γ ν hγ hν hp 0]
  ext i j
  fin_cases i <;> fin_cases j <;> fin_cases s <;>
    simp [Unitary.conjStarAlgAut_apply,signUnitary,Matrix.mul_apply,Fin.sum_univ_two,
      Matrix.star_apply]

theorem spectralMatrix_conjugate {ι : Type u_1} [Fintype ι] [DecidableEq ι]
    (U V : Matrix.unitaryGroup ι ℂ) (q : ι → ℝ) :
    Unitary.conjStarAlgAut ℂ _ U (spectralMatrix V q)=spectralMatrix (U*V) q := by
  simp only [spectralMatrix,Unitary.conjStarAlgAut_apply,Submonoid.coe_mul,star_mul,
    Matrix.mul_assoc]

/-- The two phase outputs have a single common eigenvalue distribution. -/
theorem phase_spectral (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {p : ℝ} (hp : p ∈ Set.Icc (0:ℝ) 1) :
    ∃ (q : Fin 2 → ℝ) (U : Fin 2 → Matrix.unitaryGroup (Fin 2) ℂ),
      (∀ i, 0 ≤ q i) ∧ (∑ i, q i=1) ∧
      (∀ s, phaseOutput γ ν p s=spectralMatrix (U s) q) ∧
      classicalEntropy q=g (v γ ν p) := by
  let hA := phaseOutput_state γ ν hγ hν hp 0
  let q := hA.1.isHermitian.eigenvalues
  let V := hA.1.isHermitian.eigenvectorUnitary
  have hV : phaseOutput γ ν p 0=spectralMatrix V q := hA.1.isHermitian.spectral_theorem
  refine ⟨q,fun s ↦ signUnitary s*V,?_,spectral_weights_sum hA,?_,?_⟩
  · exact hA.1.eigenvalues_nonneg
  · intro s
    rw [phaseOutput_conjugate γ ν hγ hν hp s,hV,spectralMatrix_conjugate]
  · rw [← phaseOutput_entropy γ ν hγ hν hp 0,hV,spectralMatrix_entropy]
    rfl

def meanPhaseWeights (γ ν p : ℝ) (b : Fin 2) : ℝ :=
  if b=0 then 1-((1-γ)*p+γ*ν) else (1-γ)*p+γ*ν

theorem meanPhaseWeights_nonneg (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {p : ℝ} (hp : p ∈ Set.Icc (0:ℝ) 1) (b : Fin 2) :
    0 ≤ meanPhaseWeights γ ν p b := by
  have he : 0 ≤ (1-γ)*p+γ*ν := add_nonneg (mul_nonneg (sub_nonneg.mpr hγ.2) hp.1)
    (mul_nonneg hγ.1 hν.1)
  have hu : (1-γ)*p+γ*ν ≤ 1 := by
    have h1 := mul_le_mul_of_nonneg_left hp.2 (sub_nonneg.mpr hγ.2)
    have h2 := mul_le_mul_of_nonneg_left hν.2 hγ.1
    nlinarith
  dsimp [meanPhaseWeights]
  split_ifs
  · linarith
  · exact he

theorem meanPhaseWeights_sum (γ ν p : ℝ) : ∑ b, meanPhaseWeights γ ν p b=1 := by
  simp [meanPhaseWeights,Fin.sum_univ_two]

theorem meanPhaseWeights_entropy (γ ν p : ℝ) :
    classicalEntropy (meanPhaseWeights γ ν p)=Real.binEntropy ((1-γ)*p+γ*ν) := by
  simp [classicalEntropy,meanPhaseWeights,Fin.sum_univ_two,
    Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub,add_comm]

theorem phase_mean_spectral (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {p : ℝ} (hp : p ∈ Set.Icc (0:ℝ) 1) :
    (1/2:ℝ) • phaseOutput γ ν p 0+(1/2:ℝ) • phaseOutput γ ν p 1=
      spectralMatrix 1 (meanPhaseWeights γ ν p) := by
  rw [phaseOutput_average γ ν hγ hν hp]
  simp [spectralMatrix,meanPhaseWeights]

end GAD

end

open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
namespace GAD

theorem exists_phase_code (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {p : ℝ} (hp : p ∈ Set.Icc (0:ℝ) 1)
    (q : Fin 2 → ℝ) (U : Fin 2 → Matrix.unitaryGroup (Fin 2) ℂ)
    (hq : ∀ i, 0 ≤ q i) (hs : ∑ i, q i=1)
    (hphase : ∀ s, phaseOutput γ ν p s=spectralMatrix (U s) q)
    (hent : classicalEntropy q=g (v γ ν p))
    {δ : ℝ} (hδ : 0 < δ) {n : ℕ} (hn : 0 < n) (M : ℕ) (hM : 0 < M) :
    ∃ C : Code n, C.messages=M ∧ averageError γ ν C ≤
      (9*logVariance (meanPhaseWeights γ ν p)+8*logVariance q)/((n:ℝ)*δ^2)+
        4*(M:ℝ)*Real.exp (-(n:ℝ)*(objective γ ν p-2*δ)) := by
  let qb := meanPhaseWeights γ ν p
  let w : Basis n → ℝ := fun _ ↦ ((2:ℝ)^n)⁻¹
  let A : Basis n → QMatrix n := fun s ↦ channel γ ν n (phaseState p s)
  let P := typicalProjection n (fun _ ↦ 1) qb δ
  let Q := fun s : Basis n ↦ typicalProjection n (fun k ↦ U (s k)) q δ
  have hmean : (∑ s, w s • A s)=tensorMatrix n (fun _ ↦ spectralMatrix 1 qb) := by
    simp only [w,A,phaseState_output]
    rw [tensorMatrix_average]
    simp only [phase_mean_spectral γ ν hγ hν hp,qb]
  have hA (s : Basis n) : A s=tensorMatrix n (fun k ↦ spectralMatrix (U (s k)) q) := by
    simp only [A,phaseState_output,hphase]
  have hP := typicalProjection_properties n (fun _ ↦ 1) qb
    (meanPhaseWeights_nonneg γ ν hγ hν hp) (meanPhaseWeights_sum γ ν p) hδ hn
  have hQ (s : Basis n) := typicalProjection_properties n (fun k ↦ U (s k)) q hq hs hδ hn
  have hw : ∀ s, 0 ≤ w s := fun _ ↦ by dsimp [w]; positivity
  have hw1 : ∑ s, w s=1 := phase_weights_sum n
  have hga : (∑ s, w s*(1-(P*A s).trace.re)) ≤ logVariance qb/((n:ℝ)*δ^2) := by
    have he : (∑ s, w s*(1-(P*A s).trace.re))=
        1-(P*(∑ s, w s • A s)).trace.re := by
      simp only [mul_sub,mul_one,Finset.sum_sub_distrib,hw1,Matrix.mul_sum,Matrix.mul_smul,
        Matrix.trace_sum,Matrix.trace_smul,Complex.re_sum,Complex.real_smul,Complex.mul_re,
        Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    rw [he,hmean]
    exact hP.2.2.1
  have hcb : (∑ s, w s*(1-(Q s*A s).trace.re)) ≤ logVariance q/((n:ℝ)*δ^2) := by
    calc
      _ ≤ ∑ s, w s*(logVariance q/((n:ℝ)*δ^2)) := by
        apply Finset.sum_le_sum
        intro s _
        apply mul_le_mul_of_nonneg_left _ (hw s)
        rw [hA]
        exact (hQ s).2.2.1
      _ = _ := by rw [← Finset.sum_mul,hw1,one_mul]
  have hcp : (Real.exp (-(n:ℝ)*(classicalEntropy qb-δ)) • P-
      P*(∑ s, w s • A s)*P).PosSemidef := by
    rw [hmean]
    exact hP.2.2.2
  obtain ⟨x,D,hD,hDs,he⟩ := exists_packed_measurement w hw hw1 A Q
    (fun s ↦ channel_state γ ν hγ hν n (phaseState_state hp s))
    (fun s ↦ (hQ s).1) P hP.1 (Real.exp_pos _).le (Real.exp_pos _).le
    hga hcb (fun s ↦ (hQ s).2.1) hcp M hM
  let C : Code n := {
    messages := M
    messages_pos := hM
    encoding := fun m ↦ phaseState p (x m)
    encoding_state := fun m ↦ phaseState_state hp (x m)
    decoding := D
    decoding_pos := hD
    decoding_sum := hDs }
  refine ⟨C,rfl,?_⟩
  have hexp : Real.exp (-(n:ℝ)*(classicalEntropy qb-δ))*
      Real.exp ((n:ℝ)*(classicalEntropy q+δ))=
        Real.exp (-(n:ℝ)*(objective γ ν p-2*δ)) := by
    rw [← Real.exp_add,hent,meanPhaseWeights_entropy]
    congr 1
    dsimp [objective]
    ring
  have hbound : 9*(logVariance qb/((n:ℝ)*δ^2))+8*(logVariance q/((n:ℝ)*δ^2))+
      4*(M:ℝ)*Real.exp (-(n:ℝ)*(classicalEntropy qb-δ))*Real.exp ((n:ℝ)*(classicalEntropy q+δ))=
      (9*logVariance qb+8*logVariance q)/((n:ℝ)*δ^2)+
        4*(M:ℝ)*Real.exp (-(n:ℝ)*(objective γ ν p-2*δ)) := by
    rw [mul_assoc (4*(M:ℝ)),hexp]
    ring
  rw [hbound] at he
  simpa only [averageError,C,A,Complex.re_sum] using he

end GAD

end

end OAI
