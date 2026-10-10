import OAI.Analysis.LipschitzHilbert.Packets.WeightedPacketEnergy

namespace OAI

/-! Slice energy with the full transverse decay retained. This is the
estimate required for a transverse polynomial of order 103; no horizontal
polynomial or horizontal center restriction is introduced. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace LipschitzHilbert

theorem lattice_slice_energy {N : ℕ} {κ : Type*} {ι : Fin N → Type*}
    [Fintype κ] [∀ j, Fintype (ι j)]
    (c : ∀ j, ι j → EuclideanSpace ℂ κ) (f : ∀ j, ι j → κ → SchwartzMap ℝ ℂ)
    (X Z : ∀ j, ι j → ℝ) (site : ∀ j, ι j → ℤ×ℤ) (len : Fin N → ℝ)
    (a0 b0 W y C : ℝ) (hW : 0<W) (hlen : ∀ j, 0<len j)
    (hinj : ∀ j, Function.Injective (site j))
    (hX : ∀ j i, X j i=a0+len j*(site j i).1)
    (hZ : ∀ j i, Z j i=b0+W*(site j i).2)
    (hf : ∀ j i k x, ‖f j i k x‖≤C*
      (lineEnvelope (X j i) (len j) 1 x*lineEnvelope (Z j i) W 207 y)) :
    (∑ j, ∑ k, ∫ x, ‖packetSynthesis (fun i => c j i k) (fun i => f j i k) x‖^2)≤
      ((4*Real.pi)^2*C^2*Real.pi)*
        ∑ j, len j*∑ i, ‖c j i‖^2*lineEnvelope (Z j i) W 207 y := by
  let D := (4*Real.pi)^2
  have hD : 0≤D := sq_nonneg _
  have hs (j : Fin N) (k : κ) :
      (∫ x, ‖packetSynthesis (fun i => c j i k) (fun i => f j i k) x‖^2)≤
        (D*C^2*Real.pi)*len j*∑ i, ‖c j i k‖^2*lineEnvelope (Z j i) W 207 y := by
    let rho := fun i : ι j => lineEnvelope (Z j i) W 207 y
    have hrho (i : ι j) : 0<rho i := by unfold rho lineEnvelope; positivity
    have hpoint (x : ℝ) :
        ‖packetSynthesis (fun i => c j i k) (fun i => f j i k) x‖^2≤
          D*C^2*∑ i, ‖c j i k‖^2*rho i*lineEnvelope (X j i) (len j) 1 x := by
      have hover : (∑ i, lineEnvelope (X j i) (len j) 1 x*rho i)≤D := by
        dsimp only [rho]
        simp_rw [hX,hZ]
        exact injective_tile_lattice_overlap (site j) (hinj j) a0 b0 (len j) W x y
          (hlen j).ne' hW.ne' (by norm_num) (by norm_num)
      have h := envelope_synthesis_square (fun i => c j i k) (fun i => f j i k x)
        (fun i => lineEnvelope (X j i) (len j) 1 x*rho i)
        (fun i => mul_pos (by unfold lineEnvelope; positivity) (hrho i)) hD hover
        (fun i => hf j i k x)
      simpa only [packetSynthesis_apply,smul_eq_mul,mul_assoc,mul_left_comm,mul_comm] using h
    have hi (i : ι j) : Integrable (fun x => ‖c j i k‖^2*rho i*
        lineEnvelope (X j i) (len j) 1 x) :=
      (integrable_lineEnvelope_one _ _ (hlen j)).const_mul _
    calc
      _ ≤ ∫ x, D*C^2*∑ i, ‖c j i k‖^2*rho i*lineEnvelope (X j i) (len j) 1 x :=
        integral_mono (((packetSynthesis (fun i => c j i k) (fun i => f j i k)).memLp 2 volume).integrable_norm_pow
          (by decide : (2:ℕ)≠0))
          ((integrable_finsetSum _ (fun i _ => hi i)).const_mul _) hpoint
      _ = _ := by
        rw [integral_const_mul,integral_finsetSum _ (fun i _ => hi i)]
        simp_rw [integral_const_mul,integral_lineEnvelope_one _ _ (hlen j)]
        rw [←Finset.sum_mul]
        dsimp only [rho]
        ring
  calc
    _ ≤ ∑ j, ∑ k, (D*C^2*Real.pi)*len j*
        ∑ i, ‖c j i k‖^2*lineEnvelope (Z j i) W 207 y :=
      Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => hs j k))
    _ = _ := by
      simp_rw [←Finset.mul_sum,weighted_component_energy]
      simp only [D,←Finset.mul_sum,mul_assoc]


/-- The fixed transverse polynomial is paid for by 207 powers of
transverse packet decay; one power remains for integration. -/
theorem transverse_lattice_slice_energy {N : ℕ} {κ : Type*} {ι : Fin N → Type*}
    [Fintype κ] [∀ j, Fintype (ι j)]
    (c : ∀ j, ι j → EuclideanSpace ℂ κ) (f : ∀ j, ι j → κ → SchwartzMap ℝ ℂ)
    (X Z : ∀ j, ι j → ℝ) (site : ∀ j, ι j → ℤ×ℤ) (len : Fin N → ℝ)
    (a0 b0 b W y C : ℝ) (hW : 0<W) (hlen : ∀ j, 0<len j)
    (hinj : ∀ j, Function.Injective (site j))
    (hX : ∀ j i, X j i=a0+len j*(site j i).1)
    (hZ : ∀ j i, Z j i=b0+W*(site j i).2)
    (hcenter : ∀ j i, |Z j i-b|≤2*W)
    (hf : ∀ j i k x, ‖f j i k x‖≤C*
      (lineEnvelope (X j i) (len j) 1 x*lineEnvelope (Z j i) W 207 y)) :
    polynomialWeight b (2*W) 103 y^2*
      (∑ j, ∑ k, ∫ x, ‖packetSynthesis (fun i => c j i k) (fun i => f j i k) x‖^2)≤
      ((4*Real.pi)^2*C^2*Real.pi*16^103)*
        ∑ j, len j*∑ i, ‖c j i‖^2*lineEnvelope (Z j i) W 1 y := by
  let A := (4*Real.pi)^2*C^2*Real.pi
  have hA : 0≤A := by positivity
  have he (j : Fin N) (i : ι j) := polynomialWeight_sq_mul_envelope y (Z j i)
    b W (2*W) 103 1 hW (by positivity) (by linarith) (hcenter j i)
  simp only [Nat.reduceMul,Nat.reduceAdd] at he
  calc
    _ ≤ polynomialWeight b (2*W) 103 y^2*
        (A*∑ j, len j*∑ i, ‖c j i‖^2*lineEnvelope (Z j i) W 207 y) :=
      mul_le_mul_of_nonneg_left (lattice_slice_energy c f X Z site len a0 b0 W y C hW hlen hinj hX hZ hf)
        (sq_nonneg _)
    _ = A*∑ j, len j*∑ i, ‖c j i‖^2*
        (polynomialWeight b (2*W) 103 y^2*lineEnvelope (Z j i) W 207 y) := by
      simp only [Finset.mul_sum,mul_assoc,mul_left_comm,mul_comm]
    _ ≤ A*∑ j, len j*∑ i, ‖c j i‖^2*(16^103*lineEnvelope (Z j i) W 1 y) := by
      apply mul_le_mul_of_nonneg_left _ hA
      apply Finset.sum_le_sum
      intro j _
      apply mul_le_mul_of_nonneg_left _ (hlen j).le
      exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (he j i) (sq_nonneg _))
    _ = _ := by simp only [Finset.mul_sum,A,mul_assoc,mul_left_comm,mul_comm]

end LipschitzHilbert

end

end OAI
