import Mathlib
import OAI.Computability.DirectedFeedback.Games.CanonicalAddress
import OAI.Computability.DirectedFeedback.Machines.MachineSingleOrbitCodec
import OAI.Computability.DirectedFeedback.Machines.OutputSize

namespace OAI

namespace DFVSGames.Explicit.MachineSingleOrbitBridge

open Turing DFVSGames.Reduction DFVSGames.Foundations.Complexity
open ActualSource MachineSingleOrbitCodec

namespace SingleAddress

abbrev vertexCount := Decoder.TableKeysAddressGame.vertexCount
abbrev queryAddress := Decoder.TableKeysAddressGame.queryAddress
abbrev addressEdge := Decoder.TableKeysAddressGame.addressEdge
abbrev outputInstance := Decoder.TableKeysAddressGame.outputInstance
abbrev tableOutput := Decoder.TableKeysAddressGame.tableOutput

end SingleAddress

theorem old_addressEdge_eq_double (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (ω : ActualGame.Outcome S k g) :
    AddressGame.addressEdge S k g ω = doubleConstraint (SingleAddress.addressEdge S k g ω) := by
  unfold AddressGame.addressEdge doubleConstraint SingleAddress.addressEdge
    Decoder.TableKeysAddressGame.addressEdge
  congr 1
  apply Fin.ext
  exact Encoding.sideEquiv_true_val _

theorem old_outputInstance_eq_double (S : Source) (k : Nat) {s d : Nat}
    (g : SplitGadget s d) (en : NoiseEnumeration g) :
    AddressGame.outputInstance S k g en = doubleInstance (SingleAddress.outputInstance S k g en) := by
  unfold AddressGame.outputInstance doubleInstance SingleAddress.outputInstance
    Decoder.TableKeysAddressGame.outputInstance
  congr 1
  simp only [List.map_map, Function.comp_def, ← old_addressEdge_eq_double]
  rfl

theorem old_tableOutput_eq_double (S : Source) (k : Nat) {s d : Nat}
    (T : DFVSGames.Integration.NoiseTables.Table s d) :
    AddressGame.tableOutput S k T = doubleInstance (SingleAddress.tableOutput S k T) :=
  old_outputInstance_eq_double S k _ _

def output (k : Nat) {s d : Nat} (T : DFVSGames.Integration.NoiseTables.Table s d)
    (input : SourceEncoding.Input) : DFVSGames.Foundations.Target.Instance (2 ^ s) :=
  SingleAddress.tableOutput (Source.ofList input.equations input.nonempty) k T

theorem old_output_eq_double (k : Nat) {s d : Nat}
    (T : DFVSGames.Integration.NoiseTables.Table s d) (input : SourceEncoding.Input) :
    MachineAddressGame.output k T input = doubleInstance (output k T input) :=
  old_tableOutput_eq_double _ k T

noncomputable section

def doubledComputableInPolyTime (k : Nat) {s d : Nat}
    (T : DFVSGames.Integration.NoiseTables.Table s d) :
    TM2ComputableInPolyTime SourceEncoding.inputBits
      (fun I => gameBits (doubleInstance I)) (output k T) := by
  let old := MachineAddressGame.computableInPolyTime k T
  refine {
    tm := old.tm
    inputAlphabet := old.inputAlphabet
    outputAlphabet := old.outputAlphabet
    time := old.time
    outputsFun := ?_ }
  intro input
  rw [← old_output_eq_double k T input]
  exact old.outputsFun input

def computableInPolyTime (k : Nat) {s d : Nat}
    (T : DFVSGames.Integration.NoiseTables.Table s d) :
    TM2ComputableInPolyTime SourceEncoding.inputBits gameBits (output k T) :=
  MachineSequential.composeBits (f := output k T) (g := id) (doubledComputableInPolyTime k T)
    (MachineSingleOrbitRuntime.computableInPolyTime (2 ^ s))

end

end DFVSGames.Explicit.MachineSingleOrbitBridge

namespace DFVSGames.Explicit.MachineSingleOrbitBridge

theorem workAlphabetFinite (k : Nat) {s d : Nat}
    (T : DFVSGames.Integration.NoiseTables.Table s d)
    (tape : (computableInPolyTime k T).tm.K) :
    Finite ((computableInPolyTime k T).tm.Γ tape) := by
  rcases tape with first | second
  · change Finite Bool
    infer_instance
  · rcases second with localTape | bridgeTape
    · change Finite Bool
      infer_instance
    · change Finite Bool
      infer_instance

end DFVSGames.Explicit.MachineSingleOrbitBridge

namespace DFVSGames.FromMatrixGap

open DFVSGames.Foundations Target
open DFVSGames.Foundations.Complexity
open DFVSGames.Integration
open DFVSGames.Reduction
open Explicit

noncomputable section

def reduction {ε δ : ℝ} (P : ParameterSelection.OuterParameters ε δ)
    (M : Decoder.MatrixGap.Parameters P.pStar) :
    MachineOutputContract.BinaryGapReduction ε δ := by
  classical
  have hk : 0 < M.k := M.k_pos
  let ξ := Classical.choose (P.exists_parity_error M.k hk)
  have hξspec := Classical.choose_spec (P.exists_parity_error M.k hk)
  have hξ : 0 < ξ := hξspec.1
  have hξsmall : ξ < 1 / 100 := hξspec.2.1
  have hξbudget : ξ < P.epsilon0 / (2 * M.k * P.repetitions) := hξspec.2.2
  let R := Classical.choice (Outer.BinaryParityReduction.exists_reduction ξ hξ hξsmall)
  let matrix := fun input => MachineSingleOrbitBridge.output M.k M.T (R.reduce input)
  let matrixMachine := MachineSequential.composeBits
    (f := R.reduce) (g := MachineSingleOrbitBridge.output M.k M.T)
    R.computation (MachineSingleOrbitBridge.computableInPolyTime M.k M.T)
  have matrixFinite : MachineFiniteAlphabet.FiniteAlphabet matrixMachine.tm :=
    MachineFiniteAlphabet.composeBits
      (f := R.reduce) (g := MachineSingleOrbitBridge.output M.k M.T)
      R.computation (MachineSingleOrbitBridge.computableInPolyTime M.k M.T)
      R.finiteAlphabet (MachineSingleOrbitBridge.workAlphabetFinite M.k M.T)
  have hq : 2 ≤ 2 ^ M.s := Nat.le_self_pow (by have h := M.s_pos; omega) 2
  refine FinishReduction.of_matrix_reduction P hq M.s_pos
    (Encoding.alphabetEquiv M.s).symm matrix ?_ matrixMachine matrixFinite
    ((M.k : ℚ) * ξ + P.pStar / 2)
    (P.matrix_error_budget M.k hk ξ hξbudget.le) ?_ ?_
  · intro input
    exact M.output_translations (Outer.HastadSource.asSource (R.reduce input))
  · intro input yes
    obtain ⟨assignment, hfailure⟩ :=
      Outer.BinaryParityReduction.failure_completeness R input yes
    have h := M.completeness (Outer.HastadSource.asSource (R.reduce input))
      assignment ξ hfailure
    simpa only [matrix, MachineSingleOrbitBridge.output,
      MachineSingleOrbitBridge.SingleAddress.tableOutput, Outer.HastadSource.asSource,
      Rat.cast_add, Rat.cast_mul, Rat.cast_natCast,
      Rat.cast_div, Rat.cast_ofNat] using h
  · intro input no
    exact M.sound (Outer.HastadSource.asSource (R.reduce input))
      (R.distinct input) (Outer.BinaryParityReduction.parity_soundness R input no)

end
end DFVSGames.FromMatrixGap

namespace DFVSGames.Inverse

theorem binary_kernel_finrank_lower {ℓ r : ℕ}
    (A : (Fin ℓ → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2)) :
    ℓ - r ≤ Module.finrank (ZMod 2) A.ker := by
  have hnull : Module.finrank (ZMod 2) A.range +
      Module.finrank (ZMod 2) A.ker = ℓ := by
    simpa only [Module.finrank_fin_fun] using A.finrank_range_add_finrank_ker
  have hrange : Module.finrank (ZMod 2) A.range ≤ r := by
    simpa only [Module.finrank_fin_fun] using A.range.finrank_le
  apply Nat.sub_le_iff_le_add.mpr
  calc
    ℓ = Module.finrank (ZMod 2) A.ker +
        Module.finrank (ZMod 2) A.range := hnull.symm.trans (Nat.add_comm _ _)
    _ ≤ Module.finrank (ZMod 2) A.ker + r :=
      Nat.add_le_add_left hrange _

theorem binary_kernel_card_lower {ℓ r : ℕ}
    (A : (Fin ℓ → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2)) :
    2 ^ (ℓ - r) ≤ Nat.card A.ker := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  exact Nat.pow_le_pow_right (by decide) (binary_kernel_finrank_lower A)

end DFVSGames.Inverse

namespace DFVSGames.Decoder.DimensionSelection

noncomputable section

theorem exists_logical_dimension {α η : ℝ} (hα : 0 < α) (hη : 0 < η)
    (r lower : ℕ) :
    ∃ ell : ℕ, lower ≤ ell ∧ r < ell ∧
      1 / (2 : ℝ) ^ (ell - r) < α / 8 ∧
      1 / (2 : ℝ) ^ ell < η / 4 := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
    (lt_min (show (0 : ℝ) < α / 8 by positivity)
      (show (0 : ℝ) < η / 4 by positivity))
    (show (1 / 2 : ℝ) < 1 by norm_num)
  let ell := max lower (r + n + 1)
  have hrn : r + n + 1 ≤ ell := le_max_right _ _
  have hr : r < ell := lt_of_lt_of_le (by omega) hrn
  have hnsub : n ≤ ell - r := by omega
  have hnell : n ≤ ell := hnsub.trans (Nat.sub_le _ _)
  have hpow (j : ℕ) (hj : n ≤ j) :
      1 / (2 : ℝ) ^ j < min (α / 8) (η / 4) := by
    have hmon : (1 / 2 : ℝ) ^ j ≤ (1 / 2 : ℝ) ^ n :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hj
    simpa only [one_div, inv_pow] using hmon.trans_lt hn
  exact ⟨ell, le_max_left _ _, hr,
    (hpow (ell - r) hnsub).trans_le (min_le_left _ _),
    (hpow ell hnell).trans_le (min_le_right _ _)⟩

theorem kernel_fraction_le {ell r : ℕ}
    (A : (Fin ell → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2)) [Fintype A.ker] :
    1 / (Fintype.card A.ker : ℝ) ≤ 1 / (2 : ℝ) ^ (ell - r) := by
  have hcard : (2 : ℝ) ^ (ell - r) ≤ (Fintype.card A.ker : ℝ) := by
    have h := Inverse.binary_kernel_card_lower A
    rw [Nat.card_eq_fintype_card] at h
    exact_mod_cast h
  exact one_div_le_one_div_of_le (by positivity) hcard

theorem kernel_fraction_lt {ell r : ℕ} {α : ℝ}
    (A : (Fin ell → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2)) [Fintype A.ker]
    (hsmall : 1 / (2 : ℝ) ^ (ell - r) < α / 8) :
    1 / (Fintype.card A.ker : ℝ) < α / 8 :=
  (kernel_fraction_le A).trans_lt hsmall

end
end DFVSGames.Decoder.DimensionSelection

noncomputable section
open scoped BigOperators Classical
open DFVSGames.Fourier.MatrixCharacters
open DFVSGames.Fourier.MatrixNoise

namespace DFVSGames.Decoder.NoiseSampler

section FiniteLaw

variable {Noise V : Type*} [Fintype Noise] [Fintype V]

def samplerLaw (noise : Noise → V) (v : V) : ℝ := by
  classical
  exact ∑ n, if noise n = v then (Fintype.card Noise : ℝ)⁻¹ else 0

omit [Fintype V] in
theorem samplerLaw_nonneg (noise : Noise → V) (v : V) :
    0 ≤ samplerLaw noise v := by
  classical
  unfold samplerLaw
  apply Finset.sum_nonneg
  intro n _
  split_ifs <;> positivity

omit [Fintype V] in

theorem samplerLaw_eq_count (noise : Noise → V) (v : V) :
    samplerLaw noise v =
      ((Finset.univ.filter fun n => noise n = v).card : ℝ) / Fintype.card Noise := by
  classical
  unfold samplerLaw
  rw [← Finset.sum_filter]
  simp [div_eq_mul_inv]

theorem samplerLaw_sum (noise : Noise → V) (f : V → ℝ) :
    (∑ v, samplerLaw noise v * f v) =
      (Fintype.card Noise : ℝ)⁻¹ * ∑ n, f (noise n) := by
  classical
  unfold samplerLaw
  simp_rw [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  exact (Finset.mul_sum _ _ _).symm

theorem sample_expect_eq (noise : Noise → V) (f : V → ℝ) :
    (𝔼 n, f (noise n)) = ∑ v, samplerLaw noise v * f v := by
  rw [samplerLaw_sum, Fintype.expect_eq_sum_div_card, div_eq_mul_inv, mul_comm]

theorem samplerLaw_normalized [Nonempty Noise] (noise : Noise → V) :
    ∑ v, samplerLaw noise v = 1 := by
  have h := sample_expect_eq noise (fun _ => 1)
  simpa using h.symm

theorem rat_expect_cast (f : Noise → ℚ) :
    ((𝔼 n, f n : ℚ) : ℝ) = 𝔼 n, (f n : ℝ) := by
  simp only [Finset.expect_eq_sum_div_card, Rat.cast_div, Rat.cast_sum, Rat.cast_natCast]

omit [Fintype V] in
theorem samplerLaw_eq_rat_count (noise : Noise → V) (v : V) :
    samplerLaw noise v =
      ((((Finset.univ.filter fun n => noise n = v).card : ℚ) /
        (Fintype.card Noise : ℚ) : ℚ) : ℝ) := by
  rw [samplerLaw_eq_count]
  simp only [Rat.cast_div, Rat.cast_natCast]

end FiniteLaw

variable {Noise V E : Type*} [Fintype Noise] [Fintype V]
  [AddCommGroup V] [Module F2 V]
  [AddCommGroup E] [Module F2 E]

theorem sample_kernel_eq_eigenvalue (noise : Noise → V) (S : V →ₗ[F2] E) :
    (𝔼 n, if S (noise n) = 0 then (1 : ℝ) else 0) =
      linearNoiseEigenvalue (samplerLaw noise) S := by
  classical
  exact sample_expect_eq noise (fun v => if S v = 0 then 1 else 0)

theorem detection_add_eigenvalue [Nonempty Noise]
    (noise : Noise → V) (S : V →ₗ[F2] E) :
    (𝔼 n, if S (noise n) ≠ 0 then (1 : ℝ) else 0) +
      linearNoiseEigenvalue (samplerLaw noise) S = 1 := by
  classical
  rw [← sample_kernel_eq_eigenvalue, ← Finset.expect_add_distrib]
  calc
    _ = 𝔼 _n : Noise, (1 : ℝ) := by
      apply Finset.expect_congr rfl
      intro n _
      by_cases h : S (noise n) = 0 <;> simp [h]
    _ = 1 := Fintype.expect_const 1

theorem detection_eigenvalue_le [Nonempty Noise]
    (noise : Noise → V) (S : V →ₗ[F2] E)
    (hdetect : (1 : ℝ) / 8 ≤ 𝔼 n, if S (noise n) ≠ 0 then (1 : ℝ) else 0) :
    linearNoiseEigenvalue (samplerLaw noise) S ≤ 7 / 8 := by
  have h := detection_add_eigenvalue noise S
  linarith

theorem detection_eigenvalue_le_complement [Nonempty Noise]
    (noise : Noise → V) (S : V →ₗ[F2] E) (d : ℝ)
    (hdetect : d ≤ 𝔼 n, if S (noise n) ≠ 0 then (1 : ℝ) else 0) :
    linearNoiseEigenvalue (samplerLaw noise) S ≤ 1 - d := by
  have h := detection_add_eigenvalue noise S
  linarith

theorem rational_detection_eigenvalue_le [Nonempty Noise]
    (noise : Noise → V) (S : V →ₗ[F2] E)
    (hdetect : (1 : ℚ) / 8 ≤ 𝔼 n, if S (noise n) ≠ 0 then (1 : ℚ) else 0) :
    linearNoiseEigenvalue (samplerLaw noise) S ≤ 7 / 8 := by
  apply detection_eigenvalue_le noise S
  have hcast := (Rat.cast_le (K := ℝ)).mpr hdetect
  rw [rat_expect_cast] at hcast
  simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero,
    apply_ite] using hcast

end DFVSGames.Decoder.NoiseSampler
end

namespace DFVSGames.Appendix.RankAdditivity

open Module LinearMap

variable {K W V : Type*} [Field K] [AddCommGroup W] [AddCommGroup V]
  [Module K W] [Module K V]

theorem ker_add_of_disjoint (f g : W →ₗ[K] V)
    (h : Disjoint (LinearMap.range f) (LinearMap.range g)) :
    LinearMap.ker (f + g) = LinearMap.ker f ⊓ LinearMap.ker g := by
  ext w
  constructor
  · intro hw
    have hsum : f w + g w = 0 := hw
    have hf : f w = 0 := by
      apply Submodule.disjoint_def.mp h (f w)
      · exact ⟨w, rfl⟩
      · exact ⟨-w, by simpa only [map_neg] using (eq_neg_of_add_eq_zero_left hsum).symm⟩
    have hg : g w = 0 := by simpa only [hf, zero_add] using hsum
    exact ⟨hf, hg⟩
  · rintro ⟨hf, hg⟩
    change f w + g w = 0
    change f w = 0 at hf
    change g w = 0 at hg
    rw [hf, hg, add_zero]

variable [FiniteDimensional K W] [FiniteDimensional K V]

omit [FiniteDimensional K V] in

theorem finrank_add_eq_iff (f g : W →ₗ[K] V) :
    finrank K (LinearMap.range (f + g)) =
        finrank K (LinearMap.range f) + finrank K (LinearMap.range g) ↔
      Disjoint (LinearMap.range f) (LinearMap.range g) ∧
        LinearMap.ker f ⊔ LinearMap.ker g = ⊤ := by
  have hf := f.finrank_range_add_finrank_ker
  have hg := g.finrank_range_add_finrank_ker
  have hfg := (f + g).finrank_range_add_finrank_ker
  have hker := (LinearMap.ker f).finrank_sup_add_finrank_inf_eq (LinearMap.ker g)
  constructor
  · intro hrank
    have hle := Submodule.finrank_mono (LinearMap.range_add_le f g)
    have himage := (LinearMap.range f).finrank_sup_add_finrank_inf_eq (LinearMap.range g)
    have hinf : finrank K (LinearMap.range f ⊓ LinearMap.range g : Submodule K V) = 0 := by
      omega
    have hd : Disjoint (LinearMap.range f) (LinearMap.range g) := by
      exact disjoint_iff.mpr (Submodule.finrank_eq_zero.mp hinf)
    refine ⟨hd, ?_⟩
    have heq := ker_add_of_disjoint f g hd
    rw [heq] at hfg
    apply Submodule.eq_top_of_finrank_eq
    omega
  · rintro ⟨hd, htop⟩
    rw [ker_add_of_disjoint f g hd] at hfg
    rw [htop, finrank_top] at hker
    omega

omit [FiniteDimensional K V] in

theorem range_left_le_range_add (f g : W →ₗ[K] V)
    (h : finrank K (LinearMap.range (f + g)) =
      finrank K (LinearMap.range f) + finrank K (LinearMap.range g)) :
    LinearMap.range f ≤ LinearMap.range (f + g) := by
  have hk := ((finrank_add_eq_iff f g).mp h).2
  intro v hv
  have hp : (v, (0 : V)) ∈ (LinearMap.range f).prod (LinearMap.range g) :=
    ⟨hv, Submodule.zero_mem _⟩
  rw [← LinearMap.range_prod_eq hk] at hp
  rcases hp with ⟨w, hw⟩
  have hwf : f w = v := congrArg Prod.fst hw
  have hwg : g w = 0 := congrArg Prod.snd hw
  refine ⟨w, ?_⟩
  change f w + g w = v
  rw [hwf, hwg, add_zero]

omit [FiniteDimensional K V] in

theorem ker_add_le_ker_left (f g : W →ₗ[K] V)
    (h : finrank K (LinearMap.range (f + g)) =
      finrank K (LinearMap.range f) + finrank K (LinearMap.range g)) :
    LinearMap.ker (f + g) ≤ LinearMap.ker f := by
  rw [ker_add_of_disjoint f g ((finrank_add_eq_iff f g).mp h).1]
  exact inf_le_left

def RankBelow (X Y : W →ₗ[K] V) : Prop :=
  finrank K (LinearMap.range Y) =
    finrank K (LinearMap.range X) + finrank K (LinearMap.range (Y - X))

omit [FiniteDimensional K W] [FiniteDimensional K V] in
theorem add_remainder (X Y : W →ₗ[K] V) : X + (Y - X) = Y := by
  rw [add_comm X, sub_add_cancel]

omit [FiniteDimensional K V] in
theorem rankBelow_iff (X Y : W →ₗ[K] V) :
    RankBelow X Y ↔
      Disjoint (LinearMap.range X) (LinearMap.range (Y - X)) ∧
        LinearMap.ker X ⊔ LinearMap.ker (Y - X) = ⊤ := by
  have h := finrank_add_eq_iff X (Y - X)
  rw [add_remainder] at h
  exact h

omit [FiniteDimensional K V] in
theorem range_le_of_rankBelow (X Y : W →ₗ[K] V) (h : RankBelow X Y) :
    LinearMap.range X ≤ LinearMap.range Y := by
  have h' : finrank K (LinearMap.range (X + (Y - X))) =
      finrank K (LinearMap.range X) + finrank K (LinearMap.range (Y - X)) := by
    rw [add_remainder]
    exact h
  simpa only [add_remainder] using range_left_le_range_add X (Y - X) h'

omit [FiniteDimensional K V] in
theorem ker_le_of_rankBelow (X Y : W →ₗ[K] V) (h : RankBelow X Y) :
    LinearMap.ker Y ≤ LinearMap.ker X := by
  have h' : finrank K (LinearMap.range (X + (Y - X))) =
      finrank K (LinearMap.range X) + finrank K (LinearMap.range (Y - X)) := by
    rw [add_remainder]
    exact h
  simpa only [add_remainder] using ker_add_le_ker_left X (Y - X) h'

omit [FiniteDimensional K V] in
theorem range_remainder_eq_range_on_kernel (X Y : W →ₗ[K] V) (h : RankBelow X Y) :
    LinearMap.range (Y - X) = LinearMap.range (Y.domRestrict (LinearMap.ker X)) := by
  have hc := ((rankBelow_iff X Y).mp h).2
  apply le_antisymm
  · rintro v ⟨w, hw⟩
    have ht : w ∈ LinearMap.ker X ⊔ LinearMap.ker (Y - X) := by rw [hc]; trivial
    rcases Submodule.mem_sup.mp ht with ⟨k, hk, j, hj, hkj⟩
    have hzk : (Y - X) k = (Y - X) w := by
      rw [← hkj, map_add, show (Y - X) j = 0 from hj, add_zero]
    refine ⟨⟨k, hk⟩, ?_⟩
    change Y k = v
    calc
      Y k = (Y - X) k := by
        change Y k = Y k - X k
        rw [show X k = 0 from hk, sub_zero]
      _ = (Y - X) w := hzk
      _ = v := hw
  · rintro v ⟨w, hw⟩
    refine ⟨(w : W), ?_⟩
    change Y w - X w = v
    rw [show X w = 0 from w.property, sub_zero]
    exact hw

omit [FiniteDimensional K V] in
theorem mem_ker_of_apply_mem_range_remainder (X Y : W →ₗ[K] V)
    (h : RankBelow X Y) (w : W) (hw : Y w ∈ LinearMap.range (Y - X)) :
    w ∈ LinearMap.ker X := by
  have hd := ((rankBelow_iff X Y).mp h).1
  have hz : (Y - X) w ∈ LinearMap.range (Y - X) := ⟨w, rfl⟩
  have hx : X w ∈ LinearMap.range (Y - X) := by
    have hs := (LinearMap.range (Y - X)).sub_mem hw hz
    have heq : Y w - (Y - X) w = X w := by
      simp only [LinearMap.sub_apply]
      abel
    exact heq ▸ hs
  exact Submodule.disjoint_def.mp hd (X w) ⟨w, rfl⟩ hx

end DFVSGames.Appendix.RankAdditivity

namespace DFVSGames.Appendix.CompressionCount

open Module
open DFVSGames.Integration.BinaryLinear (F2)

universe u v w

variable (U : Type u) (K : Type v) (C : Type w)
variable [AddCommGroup U] [Module F2 U]
variable [AddCommGroup K] [Module F2 K]
variable [AddCommGroup C] [Module F2 C]

def base : (U × K) →ₗ[F2] (U × C) :=
  (LinearMap.inl F2 U C).comp (LinearMap.fst F2 U K)

@[simp] theorem base_apply (p : U × K) : base U K C p = (p.1, 0) := rfl

variable {U K C}

def compress (Y : (U × K) →ₗ[F2] (U × C)) : K →ₗ[F2] C :=
  (LinearMap.snd F2 U C).comp (Y.comp (LinearMap.inr F2 U K))

@[simp] theorem compress_apply (Y : (U × K) →ₗ[F2] (U × C)) (k : K) :
    compress Y k = (Y (0, k)).2 := rfl

def Fiber (Z : K →ₗ[F2] C) :=
  {Y : (U × K) →ₗ[F2] (U × C) //
    finrank F2 Y.range = finrank F2 U + finrank F2 (Y - base U K C).range ∧
      compress Y = Z}

abbrev Parameters (Z : K →ₗ[F2] C) :=
  (Z.range →ₗ[F2] U) × (U →ₗ[F2] Z.range)

def graph (Z : K →ₗ[F2] C) (F : Z.range →ₗ[F2] U) :
    Z.range →ₗ[F2] (U × C) := F.prod Z.range.subtype

def inclusion (Z : K →ₗ[F2] C) : (U × Z.range) →ₗ[F2] (U × C) :=
  (LinearMap.id : U →ₗ[F2] U).prodMap Z.range.subtype

def lower (Z : K →ₗ[F2] C) (H : U →ₗ[F2] Z.range) :
    (U × K) →ₗ[F2] Z.range := H.coprod Z.rangeRestrict

def lift (Z : K →ₗ[F2] C) (P : Parameters (U := U) Z) :
    (U × K) →ₗ[F2] (U × C) :=
  base U K C + (graph Z P.1).comp (lower Z P.2)

@[simp] theorem lift_apply (Z : K →ₗ[F2] C) (P : Parameters (U := U) Z)
    (p : U × K) :
    lift Z P p = (p.1 + P.1 (P.2 p.1 + Z.rangeRestrict p.2),
      ((P.2 p.1 : Z.range) : C) + Z p.2) := by
  simp [lift, graph, lower]

@[simp] theorem compress_lift (Z : K →ₗ[F2] C) (P : Parameters (U := U) Z) :
    compress (lift Z P) = Z := by
  ext k
  simp

theorem graph_injective (Z : K →ₗ[F2] C) (F : Z.range →ₗ[F2] U) :
    Function.Injective (graph Z F) := by
  intro a b h
  exact Subtype.ext (congrArg Prod.snd h)

theorem inclusion_injective (Z : K →ₗ[F2] C) :
    Function.Injective (inclusion (U := U) Z) := by
  intro a b h
  exact Prod.ext (by simpa [inclusion] using congrArg Prod.fst h)
    (Subtype.ext (by simpa [inclusion] using congrArg Prod.snd h))

theorem lower_surjective (Z : K →ₗ[F2] C) (H : U →ₗ[F2] Z.range) :
    Function.Surjective (lower Z H) := by
  intro c
  obtain ⟨k, hk⟩ := Z.surjective_rangeRestrict c
  refine ⟨(0, k), ?_⟩
  simpa [lower] using hk

theorem range_lift_sub_base (Z : K →ₗ[F2] C) (P : Parameters (U := U) Z) :
    (lift Z P - base U K C).range = (graph Z P.1).range := by
  rw [lift, add_sub_cancel_left]
  exact LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr (lower_surjective Z P.2))

theorem range_lift (Z : K →ₗ[F2] C) (P : Parameters (U := U) Z) :
    (lift Z P).range = (inclusion (U := U) Z).range := by
  apply le_antisymm
  · rintro _ ⟨p, rfl⟩
    refine ⟨(p.1 + P.1 (P.2 p.1 + Z.rangeRestrict p.2),
      P.2 p.1 + Z.rangeRestrict p.2), ?_⟩
    simp [inclusion]
  · rintro _ ⟨⟨u, c⟩, rfl⟩
    obtain ⟨k, hk⟩ := Z.surjective_rangeRestrict (c - P.2 (u - P.1 c))
    refine ⟨(u - P.1 c, k), ?_⟩
    have hc : P.2 (u - P.1 c) + Z.rangeRestrict k = c := by rw [hk]; abel
    apply Prod.ext
    · change u - P.1 c + P.1 (P.2 (u - P.1 c) + Z.rangeRestrict k) = u
      rw [hc]
      abel
    · simpa [inclusion] using congrArg Subtype.val hc

variable [FiniteDimensional F2 U] [FiniteDimensional F2 K] [FiniteDimensional F2 C]

omit [FiniteDimensional F2 U] [FiniteDimensional F2 K] [FiniteDimensional F2 C] in
theorem finrank_base : finrank F2 (base U K C).range = finrank F2 U := by
  rw [base, LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr LinearMap.fst_surjective)]
  exact LinearMap.finrank_range_of_inj LinearMap.inl_injective

omit [FiniteDimensional F2 C] in
theorem lift_rank_order (Z : K →ₗ[F2] C) (P : Parameters (U := U) Z) :
    finrank F2 (lift Z P).range =
      finrank F2 U + finrank F2 (lift Z P - base U K C).range := by
  rw [range_lift, range_lift_sub_base,
    LinearMap.finrank_range_of_inj (inclusion_injective (U := U) Z),
    LinearMap.finrank_range_of_inj (graph_injective Z P.1), Module.finrank_prod]

def toFiber (Z : K →ₗ[F2] C) (P : Parameters (U := U) Z) : Fiber (U := U) Z :=
  ⟨lift Z P, lift_rank_order Z P, compress_lift Z P⟩

omit [FiniteDimensional F2 U] [FiniteDimensional F2 K] [FiniteDimensional F2 C] in
theorem lift_injective (Z : K →ₗ[F2] C) :
    Function.Injective (lift (U := U) Z) := by
  rintro ⟨F, H⟩ ⟨G, J⟩ h
  have hH : H = J := by
    ext u
    have he := congrArg (fun f => (f (u, 0)).2) h
    simpa using he
  have hF : F = G := by
    ext c
    obtain ⟨k, hk⟩ := Z.surjective_rangeRestrict c
    have he := congrArg (fun f => (f (0, k)).1) h
    simpa [hk] using he
  exact Prod.ext hF hH

theorem natCard_linearMap : Nat.card (U →ₗ[F2] C) =
    2 ^ (finrank F2 U * finrank F2 C) := by
  let e : (Fin (finrank F2 U) → C) ≃ (U →ₗ[F2] C) :=
    ((Module.finBasis F2 U).constr F2).toEquiv
  calc
    Nat.card (U →ₗ[F2] C) = Nat.card C ^ finrank F2 U := by
      rw [← Nat.card_congr e, Nat.card_fun, Nat.card_fin]
    _ = (2 ^ finrank F2 C) ^ finrank F2 U := by
      rw [Module.natCard_eq_pow_finrank (K := F2) (V := C)]
      simp [F2, Nat.card_eq_fintype_card]
    _ = 2 ^ (finrank F2 U * finrank F2 C) := by
      rw [← pow_mul, Nat.mul_comm]

omit [FiniteDimensional F2 C] in
theorem card_parameters (Z : K →ₗ[F2] C) : Nat.card (Parameters (U := U) Z) =
    2 ^ (2 * finrank F2 U * finrank F2 Z.range) := by
  rw [Nat.card_prod, natCard_linearMap, natCard_linearMap, ← pow_add]
  congr 1
  ring

omit [FiniteDimensional F2 C] in

theorem fiber_geometry (Z : K →ₗ[F2] C) (Y : Fiber (U := U) Z) :
    Disjoint (base U K C).range (Y.val - base U K C).range ∧
      (base U K C).ker ⊔ (Y.val - base U K C).ker = ⊤ := by
  apply (RankAdditivity.finrank_add_eq_iff (base U K C) (Y.val - base U K C)).mp
  have heq : base U K C + (Y.val - base U K C) = Y.val := by abel
  rw [heq, finrank_base]
  exact Y.property.1

omit [FiniteDimensional F2 C] in
theorem snd_mem_range (Z : K →ₗ[F2] C) (Y : Fiber (U := U) Z) (p : U × K) :
    (Y.val p).2 ∈ Z.range := by
  have hp : p ∈ (base U K C).ker ⊔ (Y.val - base U K C).ker := by
    rw [(fiber_geometry Z Y).2]
    trivial
  rcases Submodule.mem_sup.mp hp with ⟨a, ha, b, hb, hab⟩
  have ha0 : a.1 = 0 := congrArg Prod.fst ha
  have haeq : a = (0, a.2) := Prod.ext ha0 rfl
  have hDb : Y.val b = base U K C b := sub_eq_zero.mp hb
  refine ⟨a.2, ?_⟩
  have hcomp := LinearMap.congr_fun Y.property.2 a.2
  calc
    Z a.2 = (Y.val (0, a.2)).2 := hcomp.symm
    _ = (Y.val a).2 := congrArg (fun q => (Y.val q).2) haeq.symm
    _ = (Y.val (a + b)).2 := by simp [map_add, hDb]
    _ = (Y.val p).2 := congrArg (fun q => (Y.val q).2) hab

noncomputable def linearSection (Z : K →ₗ[F2] C) : Z.range →ₗ[F2] K :=
  Classical.choose
    (Z.rangeRestrict.exists_rightInverse_of_surjective Z.range_rangeRestrict)

omit [FiniteDimensional F2 C] in
theorem section_spec (Z : K →ₗ[F2] C) (c : Z.range) :
    Z.rangeRestrict (linearSection Z c) = c :=
  LinearMap.congr_fun (Classical.choose_spec
    (Z.rangeRestrict.exists_rightInverse_of_surjective Z.range_rangeRestrict)) c

noncomputable def extractedF (Z : K →ₗ[F2] C) (Y : Fiber (U := U) Z) :
    Z.range →ₗ[F2] U :=
  (LinearMap.fst F2 U C).comp
    (Y.val.comp ((LinearMap.inr F2 U K).comp (linearSection Z)))

def extractedH (Z : K →ₗ[F2] C) (Y : Fiber (U := U) Z) :
    U →ₗ[F2] Z.range :=
  ((LinearMap.snd F2 U C).comp (Y.val.comp (LinearMap.inl F2 U K))).codRestrict
    Z.range (fun u => snd_mem_range Z Y (u, 0))

omit [FiniteDimensional F2 C] in
theorem extracted_lower (Z : K →ₗ[F2] C) (Y : Fiber (U := U) Z) (p : U × K) :
    extractedH Z Y p.1 + Z.rangeRestrict p.2 =
      ⟨(Y.val p).2, snd_mem_range Z Y p⟩ := by
  apply Subtype.ext
  change (Y.val (p.1, 0)).2 + Z p.2 = (Y.val p).2
  rw [← LinearMap.congr_fun Y.property.2 p.2]
  change (Y.val (p.1, 0)).2 + (Y.val (0, p.2)).2 = (Y.val p).2
  rw [← Prod.snd_add, ← map_add]
  simp

omit [FiniteDimensional F2 C] in
theorem difference_ext_snd (Z : K →ₗ[F2] C) (Y : Fiber (U := U) Z)
    (p q : U × K) (h : (Y.val p).2 = (Y.val q).2) :
    (Y.val - base U K C) p = (Y.val - base U K C) q := by
  let D := Y.val - base U K C
  have hbottom : (D (p - q)).2 = 0 := by
    change ((Y.val - base U K C) (p - q)).2 = 0
    simp only [LinearMap.sub_apply, map_sub, Prod.snd_sub, base_apply]
    simpa using sub_eq_zero.mpr h
  have hzero : D (p - q) = 0 := by
    apply Submodule.disjoint_def.mp (fiber_geometry Z Y).1 (D (p - q))
    · refine ⟨((D (p - q)).1, 0), ?_⟩
      exact Prod.ext rfl hbottom.symm
    · exact ⟨p - q, rfl⟩
  exact sub_eq_zero.mp (by simpa only [map_sub] using hzero)

omit [FiniteDimensional F2 C] in
theorem lift_extracted (Z : K →ₗ[F2] C) (Y : Fiber (U := U) Z) :
    lift Z (extractedF Z Y, extractedH Z Y) = Y.val := by
  apply LinearMap.ext
  intro p
  let c : Z.range := ⟨(Y.val p).2, snd_mem_range Z Y p⟩
  have hq : (Y.val (0, linearSection Z c)).2 = (Y.val p).2 := by
    calc
      (Y.val (0, linearSection Z c)).2 = Z (linearSection Z c) :=
        LinearMap.congr_fun Y.property.2 (linearSection Z c)
      _ = (c : C) := congrArg Subtype.val (section_spec Z c)
      _ = (Y.val p).2 := rfl
  have hd := congrArg Prod.fst (difference_ext_snd Z Y p (0, linearSection Z c) hq.symm)
  change (Y.val p).1 - p.1 = (Y.val (0, linearSection Z c)).1 - 0 at hd
  apply Prod.ext
  · change p.1 + extractedF Z Y
      (extractedH Z Y p.1 + Z.rangeRestrict p.2) = (Y.val p).1
    rw [extracted_lower]
    change p.1 + (Y.val (0, linearSection Z c)).1 = (Y.val p).1
    rw [sub_zero] at hd
    rw [← hd]
    abel
  · simpa using congrArg Subtype.val (extracted_lower Z Y p)

omit [FiniteDimensional F2 C]

theorem toFiber_bijective (Z : K →ₗ[F2] C) :
    Function.Bijective (toFiber (U := U) Z) := by
  constructor
  · intro P Q h
    exact lift_injective Z (congrArg Subtype.val h)
  · intro Y
    exact ⟨(extractedF Z Y, extractedH Z Y), Subtype.ext (lift_extracted Z Y)⟩

noncomputable def fiberEquiv (Z : K →ₗ[F2] C) :
    Parameters (U := U) Z ≃ Fiber (U := U) Z :=
  Equiv.ofBijective (toFiber Z) (toFiber_bijective Z)

theorem fiber_remainder_rank (Z : K →ₗ[F2] C) (Y : Fiber (U := U) Z) :
    finrank F2 (Y.val - base U K C).range = finrank F2 Z.range := by
  obtain ⟨P, hP⟩ := (toFiber_bijective Z).2 Y
  have hY : lift Z P = Y.val := congrArg Subtype.val hP
  rw [← hY, range_lift_sub_base]
  exact LinearMap.finrank_range_of_inj (graph_injective Z P.1)

theorem fiber_rank (Z : K →ₗ[F2] C) (Y : Fiber (U := U) Z) :
    finrank F2 Y.val.range = finrank F2 U + finrank F2 Z.range := by
  rw [Y.property.1, fiber_remainder_rank]

theorem card_fiber (Z : K →ₗ[F2] C) : Nat.card (Fiber (U := U) Z) =
    2 ^ (2 * finrank F2 U * finrank F2 Z.range) := by
  rw [← Nat.card_congr (fiberEquiv (U := U) Z)]
  exact card_parameters Z

end DFVSGames.Appendix.CompressionCount

end OAI
