import OAI.NumberTheory.TwoPoint.Circuits.BitEncoding
import OAI.NumberTheory.TwoPoint.Bounds.FiniteAverages

namespace OAI

/-!
# Joint finite jitter and independent uniform bit blocks

The permutation underlying one-coordinate jitter acts independently in
every coordinate. This proves exact joint uniformity before selecting any
bits; together with CRT contraction it gives finite quantitative marginal
comparison, including arbitrary fixed non-squarefree moduli.
-/

namespace TwoPointCorrelations

open Finset

/-- Split a family of pairs into a pair of families. -/
def coordinatePairEquiv {ι : Type*} (α β : ι → Type*) :
    (∀ i, α i × β i) ≃ (∀ i, α i) × (∀ i, β i) where
  toFun x := (fun i => (x i).1, fun i => (x i).2)
  invFun x i := (x.1 i, x.2 i)
  left_inv _ := rfl
  right_inv _ := rfl

def jointJitterPermutation {ι : Type*} (s : ι → ℕ) (Q : ℕ) :
    ((∀ i, Fin (s i)) × (ι → Fin Q)) ≃ ((ι → Fin Q) × (∀ i, Fin (s i))) :=
  (coordinatePairEquiv (fun i => Fin (s i)) (fun _ => Fin Q)).symm.trans
    ((Equiv.piCongrRight (fun i => jitterPermutation (s i) Q)).trans
      (coordinatePairEquiv (fun _ => Fin Q) (fun i => Fin (s i))))

def jointJitterCode {ι : Type*} {s : ι → ℕ} {Q : ℕ}
    (r : ∀ i, Fin (s i)) (j : ι → Fin Q) : ι → Fin Q :=
  fun i => jitterCode (r i) (j i)

lemma jointJitterCode_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℕ) (Q : ℕ) (F : (ι → Fin Q) → ℝ) :
    (∑ r : ∀ i, Fin (s i), ∑ j : ι → Fin Q, F (jointJitterCode r j)) =
      (∏ i, s i : ℕ) * ∑ k : ι → Fin Q, F k := by
  rw [← Fintype.sum_prod_type']
  change (∑ x : (∀ i, Fin (s i)) × (ι → Fin Q),
    (fun y : (ι → Fin Q) × (∀ i, Fin (s i)) => F y.1) (jointJitterPermutation s Q x)) = _
  rw [(jointJitterPermutation s Q).sum_comp
    (fun y : (ι → Fin Q) × (∀ i, Fin (s i)) => F y.1), Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_pi, Fintype.card_fin,
    nsmul_eq_mul]
  rw [← Finset.mul_sum]

/-- Exact uniformity of all code coordinates under uniform residues. -/
lemma jointJitterCode_uniform {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℕ) [∀ i, NeZero (s i)] {Q : ℕ} (hQ : 0 < Q) (k : ι → Fin Q) :
    (∑ r : ∀ i, Fin (s i), (1 / (∏ i, s i : ℕ)) *
      finiteRandomKernel (@jointJitterCode ι s Q) r k) =
        1 / (Fintype.card (ι → Fin Q) : ℝ) := by
  let : Nonempty (Fin Q) := ⟨⟨0, hQ⟩⟩
  have hJ : (Fintype.card (ι → Fin Q) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hD : ((∏ i, s i : ℕ) : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne (∏ i, s i)
  unfold finiteRandomKernel
  rw [← Finset.mul_sum, ← Finset.sum_div]
  rw [jointJitterCode_sum s Q (fun z => if z = k then (1 : ℝ) else 0)]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  field_simp

/-- Evaluate joint finite jitter directly on CRT residue coordinates. -/
noncomputable def crtJitterCode {ι : Type*} (s : ι → ℕ) [∀ i, NeZero (s i)] {Q : ℕ}
    (r : ∀ i, ZMod (s i)) (j : ι → Fin Q) : ι → Fin Q :=
  jointJitterCode (fun i => (ZMod.finEquiv (s i)).symm (r i)) j

lemma crtJitterCode_uniform {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℕ) [∀ i, NeZero (s i)] {Q : ℕ} (hQ : 0 < Q) (k : ι → Fin Q) :
    kernelTransport (finiteRandomKernel (@crtJitterCode ι s _ Q)) (crtUniform s) k =
      1 / (Fintype.card (ι → Fin Q) : ℝ) := by
  let e : (∀ i, Fin (s i)) ≃ (∀ i, ZMod (s i)) :=
    Equiv.piCongrRight (fun i => (ZMod.finEquiv (s i)).toEquiv)
  calc
    _ = ∑ r : ∀ i, Fin (s i), (1 / (∏ i, s i : ℕ)) *
        finiteRandomKernel (@jointJitterCode ι s Q) r k := by
      unfold kernelTransport crtUniform
      rw [← e.sum_comp]
      apply Finset.sum_congr rfl
      intro r _
      congr 1
      unfold finiteRandomKernel crtJitterCode
      simp [e]
    _ = _ := jointJitterCode_uniform s hQ k

/-- A selected family of residue coordinates, encoded jointly, differs from
independent uniform code coordinates by at most `D/(2N)` in total variation. -/
theorem crtJitterCode_totalVariation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℕ) [∀ i, NeZero (s i)]
    (hcop : Pairwise (fun i j => (s i).Coprime (s j)))
    (A : ZMod (∏ i, s i)) (N : ℕ) (hN : 0 < N) {Q : ℕ} (hQ : 0 < Q) :
    finiteTotalVariation
      (kernelTransport (finiteRandomKernel (@crtJitterCode ι s _ Q))
        (crtJointProbability s hcop A N))
      (fun _ => 1 / (Fintype.card (ι → Fin Q) : ℝ)) ≤
        (∏ i, s i : ℕ) / (2 * (N : ℝ)) := by
  let : Nonempty (Fin Q) := ⟨⟨0, hQ⟩⟩
  have h := crt_random_projection_totalVariation s hcop A N hN (@crtJitterCode ι s _ Q)
  have heq : kernelTransport (finiteRandomKernel (@crtJitterCode ι s _ Q)) (crtUniform s) =
      (fun _ => 1 / (Fintype.card (ι → Fin Q) : ℝ)) :=
    funext (crtJitterCode_uniform s hQ)
  rw [heq] at h
  exact h

/-- Coordinatewise conversion of uniform integer cells into bit blocks. -/
noncomputable def jointBitEquiv (ι : Type*) (B : ℕ) :
    (ι → Fin (2 ^ B)) ≃ (ι → BooleanCube B) :=
  Equiv.piCongrRight (fun _ => binaryCellEquiv B)

noncomputable def crtJitterBits {ι : Type*} (s : ι → ℕ) [∀ i, NeZero (s i)] (B : ℕ)
    (r : ∀ i, ZMod (s i)) (j : ι → Fin (2 ^ B)) : ι → BooleanCube B :=
  jointBitEquiv ι B (crtJitterCode s r j)

lemma crtJitterBits_uniform {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℕ) [∀ i, NeZero (s i)] (B : ℕ) (x : ι → BooleanCube B) :
    kernelTransport (finiteRandomKernel (crtJitterBits s B)) (crtUniform s) x =
      1 / (Fintype.card (ι → BooleanCube B) : ℝ) := by
  have heq (r : ∀ i, ZMod (s i)) :
      finiteRandomKernel (crtJitterBits s B) r x =
        finiteRandomKernel (@crtJitterCode ι s _ (2 ^ B)) r ((jointBitEquiv ι B).symm x) := by
    unfold finiteRandomKernel
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    have heq : crtJitterBits s B r j = x ↔
        crtJitterCode s r j = (jointBitEquiv ι B).symm x := by
      change jointBitEquiv ι B (crtJitterCode s r j) = x ↔ _
      exact (jointBitEquiv ι B).eq_symm_apply.symm
    simp only [heq]
  unfold kernelTransport
  simp_rw [heq]
  change kernelTransport (finiteRandomKernel (@crtJitterCode ι s _ (2 ^ B)))
    (crtUniform s) ((jointBitEquiv ι B).symm x) = _
  rw [crtJitterCode_uniform s (by positivity)]
  rw [Fintype.card_congr (jointBitEquiv ι B)]

/-- Exact joint uniform bit law and the interval comparison error, before
projecting to any subset of these bits. -/
theorem crtJitterBits_totalVariation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → ℕ) [∀ i, NeZero (s i)]
    (hcop : Pairwise (fun i j => (s i).Coprime (s j)))
    (A : ZMod (∏ i, s i)) (N : ℕ) (hN : 0 < N) (B : ℕ) :
    finiteTotalVariation
      (kernelTransport (finiteRandomKernel (crtJitterBits s B)) (crtJointProbability s hcop A N))
      (fun _ => 1 / (Fintype.card (ι → BooleanCube B) : ℝ)) ≤
        (∏ i, s i : ℕ) / (2 * (N : ℝ)) := by
  let : Nonempty (Fin (2 ^ B)) := ⟨⟨0, by positivity⟩⟩
  have h := crt_random_projection_totalVariation s hcop A N hN (crtJitterBits s B)
  have heq : kernelTransport (finiteRandomKernel (crtJitterBits s B)) (crtUniform s) =
      (fun _ => 1 / (Fintype.card (ι → BooleanCube B) : ℝ)) :=
    funext (crtJitterBits_uniform s B)
  rw [heq] at h
  exact h

end TwoPointCorrelations

end OAI
