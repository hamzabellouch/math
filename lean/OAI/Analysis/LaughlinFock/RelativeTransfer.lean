import Mathlib
import OAI.Analysis.LaughlinFock.RowTraces

namespace OAI

/-! Relative Transfer. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open Filter Topology

 

structure ComparisonRow where
  t : Fin 8
  ell : ℝ
  alpha : RowEntry t.val → ℝ

 
def fourSpinRatio (Q D : ℕ) : ℝ :=
  (4 * (Q : ℝ) - 1 - 2 * (D : ℝ)) / (2 * (Q : ℝ) - 1)

theorem fourSpinRatio_tendsto (D : ℕ) :
    Tendsto (fun Q => fourSpinRatio Q D) atTop (𝓝 2) := by
  have h1 := tendsto_const_div_atTop_nhds_zero_nat (1+2*(D:ℝ))
  have h2 := tendsto_const_div_atTop_nhds_zero_nat (1:ℝ)
  have hh : Tendsto (fun Q : ℕ => (4-(1+2*(D:ℝ))/Q)/(2-1/(Q:ℝ))) atTop (𝓝 2) := by
    convert ((tendsto_const_nhds (x := (4:ℝ))).sub h1).div
      ((tendsto_const_nhds (x := (2:ℝ))).sub h2) (show (2:ℝ)-0 ≠ 0 by norm_num)
      using 1; first | rfl | norm_num
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with Q hQ
  have hn : (Q : ℝ) ≠ 0 := by exact_mod_cast (by omega : Q ≠ 0)
  have hqr : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hd : 2*(Q:ℝ)-1 ≠ 0 := by linarith
  have hd' : 2-1/(Q:ℝ) ≠ 0 := by rw [ne_eq, sub_eq_zero, eq_div_iff hn]; linarith
  unfold fourSpinRatio
  field_simp [hn, hd, hd']
  ring

theorem fourSpinRatio_eq_dimensions {Q D : ℕ} (hQ : 1 ≤ Q) (hD : D ≤ Q) :
    fourSpinRatio Q D = ((4*Q-1-2*D : ℕ) : ℝ) / ((2*Q-1 : ℕ) : ℝ) := by
  have h1 : 1 ≤ 4*Q := by omega
  have h2 : 2*D ≤ 4*Q-1 := by omega
  have h3 : 1 ≤ 2*Q := by omega
  simp only [fourSpinRatio, Nat.cast_sub h1, Nat.cast_sub h2, Nat.cast_sub h3,
    Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]

 
def targetCopy (D : ℕ) : Matrix (CopyLabel D) (CopyLabel D) ℂ := fun r s =>
  if r.val.val=1 ∧ s.val.val=1 then 1 else 0

theorem targetCopy_hermitian (D : ℕ) : (targetCopy D).IsHermitian := by
  classical
  ext r s
  simp [targetCopy, Matrix.conjTranspose_apply, and_comm]

 

def fourComparison {ι : Type*} [Fintype ι] (rows : ι → ComparisonRow)
    (ε : ℝ) (Q D : ℕ) : Matrix (CopyLabel D) (CopyLabel D) ℂ :=
  (fourSpinRatio Q D : ℂ) • targetCopy D -
    Matrix.of (fun r s => ((∑ i, rowFourTrace Q D (rows i).t.val (rows i).alpha r s : ℝ) : ℂ)) +
      (ε : ℂ) • 1

 
def planarFourComparison {ι : Type*} [Fintype ι] (rows : ι → ComparisonRow)
    (ε : ℝ) (D : ℕ) : Matrix (CopyLabel D) (CopyLabel D) ℂ :=
  (2 : ℂ) • targetCopy D -
    Matrix.of (fun r s => ((∑ i, planarRowFourTrace D (rows i).t.val (rows i).alpha r s : ℝ) : ℂ)) +
      (ε : ℂ) • 1

theorem fourComparison_hermitian {ι : Type*} [Fintype ι] (rows : ι → ComparisonRow)
    (ε : ℝ) (Q D : ℕ) : (fourComparison rows ε Q D).IsHermitian := by
  have h : (Matrix.of (fun r s => ((∑ i, rowFourTrace Q D (rows i).t.val (rows i).alpha r s : ℝ) : ℂ))).IsHermitian := by
    ext r s
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, Complex.star_def, Complex.conj_ofReal]
    apply congrArg (fun x : ℝ => (x : ℂ))
    apply Finset.sum_congr rfl
    intro i _
    exact congrFun (congrFun (rowFourTrace_symmetric Q D (rows i).t.val (rows i).alpha) r) s
  exact ((targetCopy_hermitian D).smul (show IsSelfAdjoint (fourSpinRatio Q D : ℂ) by simp [IsSelfAdjoint])).sub h |>.add
    (Matrix.isHermitian_one.smul (show IsSelfAdjoint (ε : ℂ) by simp [IsSelfAdjoint]))

theorem planarFourComparison_hermitian {ι : Type*} [Fintype ι]
    (rows : ι → ComparisonRow) (ε : ℝ) (D : ℕ) :
    (planarFourComparison rows ε D).IsHermitian := by
  have h : (Matrix.of (fun r s => ((∑ i, planarRowFourTrace D (rows i).t.val (rows i).alpha r s : ℝ) : ℂ))).IsHermitian := by
    ext r s
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, Complex.star_def, Complex.conj_ofReal]
    apply congrArg (fun x : ℝ => (x : ℂ))
    apply Finset.sum_congr rfl
    intro i _
    exact congrFun (congrFun (planarRowFourTrace_symmetric D (rows i).t.val (rows i).alpha) r) s
  exact ((targetCopy_hermitian D).smul (show IsSelfAdjoint (2 : ℂ) by norm_num)).sub h |>.add
    (Matrix.isHermitian_one.smul (show IsSelfAdjoint (ε : ℂ) by simp [IsSelfAdjoint]))

theorem fourComparison_tendsto {ι : Type*} [Fintype ι] (rows : ι → ComparisonRow)
    (ε : ℝ) (D : ℕ) :
    Tendsto (fun Q => fourComparison rows ε Q D) atTop (𝓝 (planarFourComparison rows ε D)) := by
  apply tendsto_pi_nhds.mpr
  intro r
  apply tendsto_pi_nhds.mpr
  intro s
  have hf := Complex.continuous_ofReal.continuousAt.tendsto.comp (fourSpinRatio_tendsto D)
  have ht := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_finsetSum Finset.univ (fun i _ => rowFourTrace_tendsto D (rows i).t.val (rows i).alpha r s))
  simpa only [fourComparison, planarFourComparison, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, Function.comp_apply, Complex.ofReal_ofNat] using
      ((hf.mul_const (targetCopy D r s)).sub ht).add_const ((ε : ℂ)*(1 : Matrix (CopyLabel D) (CopyLabel D) ℂ) r s)

 

def localCopyMatrix (D Q : ℕ) : Matrix (CopyLabel D) (FourHighestShell 24 D) ℂ := fun r b =>
  sphericalCopyCoefficient Q D D r.val.val b.val.1.val b.val.2.val.1.val b.val.2.val.2.val

def planarLocalCopyMatrix (D : ℕ) : Matrix (CopyLabel D) (FourHighestShell 24 D) ℂ := fun r b =>
  planarCopyCoefficient D D r.val.val b.val.1.val b.val.2.val.1.val b.val.2.val.2.val

theorem localCopyMatrix_tendsto (D : ℕ) : Tendsto (localCopyMatrix D) atTop (𝓝 (planarLocalCopyMatrix D)) := by
  apply tendsto_pi_nhds.mpr
  intro r
  apply tendsto_pi_nhds.mpr
  intro b
  exact Complex.continuous_ofReal.continuousAt.tendsto.comp
    (sphericalCopyCoefficient_tendsto D D r.val.val b.val.1.val b.val.2.val.1.val b.val.2.val.2.val)

 

def planarHighestFourAnnihilator (D : ℕ) (r : CopyLabel D) : FockMatrix 24 :=
  ∑ b : FourHighestShell 24 D, planarLocalCopyMatrix D r b •
    (annihilator 24 b.val.2.val.2 * annihilator 24 b.val.2.val.1 * limitPairAnnihilator 24 b.val.1.val)

theorem planarHighestFourAnnihilator_mem (D : ℕ) (r : CopyLabel D) :
    planarHighestFourAnnihilator D r ∈ AnnihilationSpace 24 4 := by
  apply Submodule.sum_mem
  intro b _
  apply Submodule.smul_mem
  exact annihilationSpace_mul 24 2 2 (limitPairAnnihilator_mem 24 b.val.1.val)
    (annihilationSpace_mul 24 1 1 (annihilator_mem 24 b.val.2.val.1) (annihilator_mem 24 b.val.2.val.2))

 

def planarFourWedgeMatrix (D : ℕ) : Matrix (SectorOccupation 24 4) (CopyLabel D) ℂ :=
  fun A r => annihilatorVector 24 4 (planarHighestFourAnnihilator D r) A

def planarFourGram (D : ℕ) : Matrix (CopyLabel D) (CopyLabel D) ℂ :=
  (planarFourWedgeMatrix D)ᴴ * planarFourWedgeMatrix D

theorem planarFourWedgeMatrix_annihilator_column (D : ℕ) (r : CopyLabel D) :
    wedgeAnnihilator 24 4 (fun A => planarFourWedgeMatrix D A r) =
      planarHighestFourAnnihilator D r :=
  wedgeAnnihilator_annihilatorVector 24 4 _ (planarHighestFourAnnihilator_mem D r)

 

theorem planarFourCertificate_lift {ι : Type*} [Fintype ι] (rows : ι → ComparisonRow)
    (ε : ℝ) (D : ℕ)
    (h : (planarFourGram D * planarFourComparison rows ε D * planarFourGram D).PosSemidef) :
    (∑ r, ∑ s, planarFourComparison rows ε D r s •
      ((planarHighestFourAnnihilator D r)ᴴ * planarHighestFourAnnihilator D s)).PosSemidef := by
  have hh := exteriorLift_of_gram_certificate 24 4 (planarFourWedgeMatrix D)
    (planarFourComparison rows ε D) (planarFourComparison_hermitian rows ε D) h
  simpa only [planarFourWedgeMatrix_annihilator_column] using hh

 

def fourShellExtension (D R : ℕ) : FourHighestShell 24 D → FourHighestShell (24+R) D := fun b =>
  ⟨(⟨b.val.1.val, by have := b.val.1.isLt; omega⟩,
    ⟨(localOrbital 24 R b.val.2.val.1, localOrbital 24 R b.val.2.val.2), b.val.2.property⟩), b.property⟩

theorem fourShellExtension_injective (D R : ℕ) : Function.Injective (fourShellExtension D R) := by
  intro b c he
  apply Subtype.ext
  apply Prod.ext
  · apply Fin.ext
    exact congrArg (fun x => x.val.1.val) he
  · apply Subtype.ext
    apply Prod.ext
    · apply Fin.ext
      exact congrArg (fun x => x.val.2.val.1.val) he
    · apply Fin.ext
      exact congrArg (fun x => x.val.2.val.2.val) he

theorem fourShellExtension_surjective {D : ℕ} (hD : D ≤ 23) (R : ℕ) :
    Function.Surjective (fourShellExtension D R) := by
  intro b
  have hb := b.property
  let c : FourHighestShell 24 D :=
    ⟨(⟨b.val.1.val, by omega⟩,
      ⟨(⟨b.val.2.val.1.val, by omega⟩, ⟨b.val.2.val.2.val, by omega⟩),
        b.val.2.property⟩), hb⟩
  refine ⟨c, ?_⟩
  apply Subtype.ext
  apply Prod.ext
  · apply Fin.ext
    rfl
  · apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext <;> rfl

 

theorem highestFourAnnihilator_local_sum {D : ℕ} (hD : D ≤ 23) (R : ℕ) (r : CopyLabel D) :
    highestFourAnnihilator (24+R) D r =
      ∑ b : FourHighestShell 24 D, localCopyMatrix D (24+R) r b •
        (annihilator (24+R) (localOrbital 24 R b.val.2.val.2) *
         annihilator (24+R) (localOrbital 24 R b.val.2.val.1) * pairAnnihilator (24+R) b.val.1.val) := by
  classical
  unfold highestFourAnnihilator
  let e : FourHighestShell 24 D ≃ FourHighestShell (24+R) D :=
    Equiv.ofBijective (fourShellExtension D R)
      ⟨fourShellExtension_injective D R, fourShellExtension_surjective hD R⟩
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro b _
  rfl

 

theorem fourComparison_relative_transfer {ι : Type*} [Fintype ι]
    (rows : ι → ComparisonRow) (ε : ℝ) {D : ℕ} (hD : D ≤ 23)
    (hCertificate : (planarFourGram D * planarFourComparison rows ε D * planarFourGram D).PosSemidef) :
    ∃ ρ : ℕ → ℝ, (∀ Q, 0 ≤ ρ Q) ∧ Tendsto ρ atTop (𝓝 0) ∧
      ∀ Q, 24 ≤ Q →
        ((∑ r, ∑ s, fourComparison rows ε Q D r s •
          ((highestFourAnnihilator Q D r)ᴴ * highestFourAnnihilator Q D s)) +
            ρ Q • partialHamiltonian Q 24).PosSemidef := by
  have hb (b : FourHighestShell 24 D) : b.val.1.val < 24 := by
    have := b.property
    omega
  obtain ⟨ρ, hρ0, hρlim, hρ⟩ := fock_transfer_of_limitpositive 24 24 (by norm_num) le_rfl
    (fun b : FourHighestShell 24 D => b.val.1.val)
    (fun b => b.val.2.val.1) (fun b => b.val.2.val.2) hb
    (localCopyMatrix D) (planarLocalCopyMatrix D)
    (fun Q => fourComparison rows ε Q D) (planarFourComparison rows ε D)
    (localCopyMatrix_tendsto D) (fourComparison_tendsto rows ε D)
    (fun Q => fourComparison_hermitian rows ε Q D) (planarFourComparison_hermitian rows ε D)
    (planarFourCertificate_lift rows ε D hCertificate)
  refine ⟨ρ, hρ0, hρlim, ?_⟩
  intro Q hQ
  obtain ⟨R, rfl⟩ := Nat.exists_eq_add_of_le hQ
  simpa only [← highestFourAnnihilator_local_sum hD R] using hρ R

 

theorem fourComparison_uniform_transfer {ι : Type*} [Fintype ι]
    (rows : ι → ComparisonRow) (ε : ℝ)
    (hCertificate : ∀ D, 1 ≤ D → D ≤ 23 →
      (planarFourGram D * planarFourComparison rows ε D * planarFourGram D).PosSemidef) :
    ∃ ρ : ℕ → ℝ, (∀ Q, 0 ≤ ρ Q) ∧ Tendsto ρ atTop (𝓝 0) ∧
      ∀ D, 1 ≤ D → D ≤ 23 → ∀ Q, 24 ≤ Q →
        ((∑ r, ∑ s, fourComparison rows ε Q D r s •
          ((highestFourAnnihilator Q D r)ᴴ * highestFourAnnihilator Q D s)) +
            ρ Q • partialHamiltonian Q 24).PosSemidef := by
  classical
  have hh (d : Fin 23) := fourComparison_relative_transfer rows ε
    (by omega : d.val+1 ≤ 23) (hCertificate (d.val+1) (by omega) (by omega))
  choose ρ hρpos hρlim hρbound using hh
  refine ⟨fun Q => ∑ d, ρ d Q, ?_, ?_, ?_⟩
  · intro Q
    exact Finset.sum_nonneg (fun d _ => hρpos d Q)
  · simpa only [Finset.sum_const_zero] using
      tendsto_finsetSum Finset.univ (fun d _ => hρlim d)
  · intro D hD0 hD Q hQ
    let d : Fin 23 := ⟨D-1, by omega⟩
    have hd : d.val+1 = D := by dsimp [d]; omega
    have hle : ρ d Q ≤ ∑ e, ρ e Q :=
      Finset.single_le_sum (fun e _ => hρpos e Q) (Finset.mem_univ d)
    have h := hρbound d Q hQ
    rw [hd] at h
    have h' := h.add ((partialHamiltonian_posSemidef Q 24).smul (sub_nonneg.mpr hle))
    convert h' using 1
    simp only [sub_smul]
    abel

end LaughlinFock
end

end OAI
