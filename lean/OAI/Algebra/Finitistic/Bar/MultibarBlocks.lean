import OAI.Algebra.Finitistic.Bar.MultibarSigns

namespace OAI
open scoped TensorProduct
open TensorProduct TrivSqZeroExt
noncomputable section

namespace DerivedBar.Multibar
universe u

/-- `false` records a D slot, `true` an X slot. The leading D is separate. -/
def count : List Bool → ℕ
  | [] => 0
  | false :: p => count p
  | true :: p => count p + 1

/-- Number of ordered pairs consisting of a D slot followed by an X slot. -/
def inversions : List Bool → ℕ
  | [] => 0
  | false :: p => count p + inversions p
  | true :: p => inversions p

/-- The r+1 block lengths, with no empty-list ambiguity at r=0. -/
def Blocks : ℕ → Type
  | 0 => ℕ
  | r+1 => ℕ × Blocks r

def total : (r : ℕ) → Blocks r → ℕ
  | 0, i => i
  | r+1, (i, tail) => i + total r tail

/-- This recursive sum is exactly Σⱼ (r-j)iⱼ. -/
def exponent : (r : ℕ) → Blocks r → ℕ
  | 0, _ => 0
  | r+1, (i, tail) => (r+1)*i + exponent r tail

def pattern : (r : ℕ) → Blocks r → List Bool
  | 0, i => List.replicate i false
  | r+1, (i, tail) => List.replicate i false ++ true :: pattern r tail

@[simp] theorem count_bases (i : ℕ) (p : List Bool) :
    count (List.replicate i false ++ p) = count p := by
  induction i with
  | zero => rfl
  | succ i ih => simpa [List.replicate_succ, count] using ih

@[simp] theorem inversions_bases (i : ℕ) (p : List Bool) :
    inversions (List.replicate i false ++ p) = i * count p + inversions p := by
  induction i with
  | zero => simp
  | succ i ih =>
    simp only [List.replicate_succ, List.cons_append, inversions, count_bases, ih]
    rw [Nat.succ_mul]
    omega

@[simp] theorem count_pattern (r : ℕ) (b : Blocks r) : count (pattern r b) = r := by
  induction r with
  | zero => simpa [pattern, count] using count_bases b []
  | succ r ih =>
    rcases b with ⟨i, tail⟩
    simp [pattern, count, ih]

/-- The actual word length agrees with source cohomological degree -r-Σiⱼ. -/
@[simp] theorem length_pattern (r : ℕ) (b : Blocks r) :
    (pattern r b).length = r + total r b := by
  induction r with
  | zero =>
    change ℕ at b
    simp [pattern, total]
  | succ r ih =>
    rcases b with ⟨i, tail⟩
    simp only [pattern, List.length_append, List.length_replicate, List.length_cons, ih, total]
    omega

/-- The combinatorial rescaling is exactly the component factor in prop:bar-splitting. -/
@[simp] theorem inversions_pattern (r : ℕ) (b : Blocks r) :
    inversions (pattern r b) = exponent r b := by
  induction r with
  | zero =>
    change ℕ at b
    simpa [pattern, exponent, inversions, count] using inversions_bases b []
  | succ r ih =>
    rcases b with ⟨i, tail⟩
    simp [pattern, inversions, count, exponent, ih, Nat.mul_comm]

variable (k D X N : Type u) [Field k] [Ring D] [Algebra k D]
  [AddCommGroup X] [Module k X] [Module D X] [Module Dᵐᵒᵖ X]
  [SMulCommClass D Dᵐᵒᵖ X] [IsScalarTower k D X] [IsScalarTower k Dᵐᵒᵖ X]
  [AddCommGroup N] [Module k N]

/-- Genuine iterated tensors over k for a prescribed D/X pattern, ending in N.
No ordinary tensor over D is used in these bar terms. -/
@[reducible] def patternTerm : List Bool → ModuleCat k
  | [] => ModuleCat.of k N
  | false :: p => ModuleCat.of k (D ⊗[k] patternTerm p)
  | true :: p => ModuleCat.of k (X ⊗[k] patternTerm p)

/-- Inclusion of each D/X tensor into the actual A bar term. -/
def embed : (p : List Bool) → patternTerm k D X N p →ₗ[k]
    DerivedBar.term k (TrivSqZeroExt D X) N p.length
  | [] => LinearMap.id
  | false :: p => TensorProduct.map (inlAlgHom k D X).toLinearMap (embed p)
  | true :: p => TensorProduct.map ((inrHom D X).restrictScalars k) (embed p)

/-- Slotwise projection back to the prescribed tensor; this proves no tensor relations were lost. -/
def extract : (p : List Bool) → DerivedBar.term k (TrivSqZeroExt D X) N p.length →ₗ[k]
    patternTerm k D X N p
  | [] => LinearMap.id
  | false :: p => TensorProduct.map (fstHom k D X).toLinearMap (extract p)
  | true :: p => TensorProduct.map ((sndHom D X).restrictScalars k) (extract p)

/-- Every block inclusion has an actual linear left inverse. -/
theorem extract_embed (p : List Bool) (v : patternTerm k D X N p) :
    extract k D X N p (embed k D X N p v) = v := by
  induction p with
  | nil => rfl
  | cons b p ih =>
    cases b <;>
      dsimp only [patternTerm, embed, extract] at * <;>
      induction v using TensorProduct.inductionOn with
      | tmul a v =>
        change a ⊗ₜ[k] extract k D X N p (embed k D X N p v) = a ⊗ₜ[k] v
        rw [ih]
      | add v w hv hw => simp only [map_add, hv, hw]

/-- Each tensor embeds into its correct count subspace. -/
theorem embed_mem (p : List Bool) (v : patternTerm k D X N p) :
    embed k D X N p v ∈ SquareZero.weight k D X N p.length (count p) := by
  induction p with
  | nil => exact Submodule.subset_span (SquareZero.Word.nil v)
  | cons b p ih =>
    cases b <;>
      dsimp only [patternTerm, embed, extract] at * <;>
      induction v using TensorProduct.inductionOn with
      | tmul a v =>
        first
        | exact SquareZero.base_tmul_mem a (ih v)
        | exact SquareZero.ideal_tmul_mem a (ih v)
      | add v w hv hw =>
        simpa only [map_add] using Submodule.add_mem _ hv hw

/-- Evaluation of the constructed sign operator on genuine pattern tensors. -/
theorem signedProjection_embed (p : List Bool) (v : patternTerm k D X N p) :
    SquareZero.signedProjection k D X N p.length (count p) (embed k D X N p v) =
      (-1 : k)^(inversions p) • embed k D X N p v := by
  induction p with
  | nil => simp [embed, count, inversions, SquareZero.signedProjection]
  | cons b p ih =>
    cases b <;>
      dsimp only [patternTerm, embed, extract] at * <;>
      induction v using TensorProduct.inductionOn with
      | tmul a v =>
        first
        | change SquareZero.signedProjection k D X N (p.length+1) (count p)
            ((inl a : TrivSqZeroExt D X) ⊗ₜ[k] embed k D X N p v) = _
          rw [SquareZero.signedProjection_base, ih, TensorProduct.tmul_smul, smul_smul,
            ← pow_add]
          rfl
        | change SquareZero.signedProjection k D X N (p.length+1) (count p+1)
            ((inr a : TrivSqZeroExt D X) ⊗ₜ[k] embed k D X N p v) = _
          rw [SquareZero.signedProjection_ideal_succ, ih, TensorProduct.tmul_smul]
          rfl
      | add v w hv hw => simp only [map_add, hv, hw, smul_add]

/-- The source block tensor, including the exterior D coefficient. -/
abbrev blockTerm (r : ℕ) (b : Blocks r) := D ⊗[k] patternTerm k D X N (pattern r b)

def blockEmbed (r : ℕ) (b : Blocks r) : blockTerm k D X N r b →ₗ[D]
    D ⊗[k] DerivedBar.term k (TrivSqZeroExt D X) N (pattern r b).length :=
  AlgebraTensorModule.lTensor D D (embed k D X N (pattern r b))

def blockExtract (r : ℕ) (b : Blocks r) :
    D ⊗[k] DerivedBar.term k (TrivSqZeroExt D X) N (pattern r b).length →ₗ[D]
      blockTerm k D X N r b :=
  AlgebraTensorModule.lTensor D D (extract k D X N (pattern r b))

theorem blockExtract_embed (r : ℕ) (b : Blocks r) (v : blockTerm k D X N r b) :
    blockExtract k D X N r b (blockEmbed k D X N r b v) = v := by
  induction v using TensorProduct.inductionOn with
  | tmul d v =>
    change d ⊗ₜ[k] extract k D X N (pattern r b) (embed k D X N (pattern r b) v) = _
    rw [extract_embed]
  | add v w hv hw => simp only [map_add, hv, hw]

/-- Actual block tensors inject, with no D-flatness hypothesis. -/
theorem blockEmbed_injective (r : ℕ) (b : Blocks r) :
    Function.Injective (blockEmbed k D X N r b) :=
  Function.LeftInverse.injective (blockExtract_embed k D X N r b)

theorem blockEmbed_mem (r : ℕ) (b : Blocks r) (v : blockTerm k D X N r b) :
    blockEmbed k D X N r b v ∈
      SquareZero.twoSidedWeight k D X N (pattern r b).length r := by
  induction v using TensorProduct.inductionOn with
  | tmul d v =>
    have h := SquareZero.tensor_weight_mem d (embed_mem k D X N (pattern r b) v)
    simpa only [count_pattern, blockEmbed, AlgebraTensorModule.lTensor_tmul] using h
  | add v w hv hw => simpa only [map_add] using Submodule.add_mem _ hv hw

/-- The D-linear rescaling on each source block is exactly (-1)^(Σⱼ(r-j)iⱼ). -/
theorem sign_on_block (r : ℕ) (b : Blocks r) (v : blockTerm k D X N r b) :
    SquareZero.twoSidedSignedProjection k D X N (pattern r b).length r
      (blockEmbed k D X N r b v) =
        (-1 : k)^(exponent r b) • blockEmbed k D X N r b v := by
  induction v using TensorProduct.inductionOn with
  | tmul d v =>
    change d ⊗ₜ[k] SquareZero.signedProjection k D X N (pattern r b).length r
      (embed k D X N (pattern r b) v) = _
    have h := signedProjection_embed k D X N (pattern r b) v
    rw [count_pattern, inversions_pattern] at h
    rw [h, TensorProduct.tmul_smul]
    rfl
  | add v w hv hw => simp only [map_add, hv, hw, smul_add]
end DerivedBar.Multibar

end

end OAI
