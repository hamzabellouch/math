import OAI.Analysis.Cotype.BinaryCoordinates

namespace OAI

noncomputable section

open scoped BigOperators
namespace Cotype
variable {𝕜 : Type*} [Field 𝕜]
variable {ι κ ν : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype ν] [DecidableEq ν]

theorem tagged_frames_feasible (f : ι ↪ ν) (g : κ ↪ ν)
    (hfg : ∀ i j, f i ≠ g j) (D : ι → κ → 𝕜) :
    ∃ (U : ι → ν → 𝕜) (V : κ → ν → 𝕜),
      LinearIndependent 𝕜 U ∧ LinearIndependent 𝕜 V ∧
      ∀ i j, coordinateDual (V j) (U i) = D i j := by
  let U : ι → ν → 𝕜 := fun i => Pi.single (f i) 1
  let V : κ → ν → 𝕜 := fun j => (∑ i, D i j • U i) + Pi.single (g j) 1
  have hUf (i k : ι) : U i (f k) = if i = k then 1 else 0 := by
    simp [U, Pi.single_apply, f.injective.eq_iff, eq_comm]
  have hUg (i : ι) (j : κ) : U i (g j) = 0 := by
    simp [U, Ne.symm (hfg i j)]
  have hVf (i : ι) (j : κ) : V j (f i) = D i j := by
    simp [V, Finset.sum_apply, hUf, hfg i j]
  have hVg (j k : κ) : V j (g k) = if j = k then 1 else 0 := by
    simp [V, Finset.sum_apply, hUg, Pi.single_apply, g.injective.eq_iff, eq_comm]
  refine ⟨U,V,?_,?_,?_⟩
  · apply Fintype.linearIndependent_iff.mpr
    intro c hc i
    have h := congrFun hc (f i)
    simpa [Finset.sum_apply, hUf] using h
  · apply Fintype.linearIndependent_iff.mpr
    intro c hc j
    have h := congrFun hc (g j)
    simpa [Finset.sum_apply, hVg] using h
  · intro i j
    simpa [coordinateDual_apply, U, Pi.single_apply] using hVf i j

theorem binary_frames_feasible {n r s : ℕ} (hn : r+s ≤ n)
    (D : Fin r → Fin s → ZMod 2) :
    ∃ (U : Fin r → Cube n) (V : Fin s → Cube n),
      BinaryFrame U ∧ BinaryFrame V ∧
      ∀ i j, character (V j) (U i) = binarySign (D i j) := by
  let f : Fin r ↪ Fin n := ⟨fun i => Fin.castLE hn (Fin.castAdd s i), by
    intro i j h; apply Fin.ext; exact congrArg (fun x : Fin n => x.val) h⟩
  let g : Fin s ↪ Fin n := ⟨fun j => Fin.castLE hn (Fin.natAdd r j), by
    intro i j h; apply Fin.ext
    have hh := congrArg Fin.val h
    change r + i.val = r + j.val at hh
    omega⟩
  have hfg : ∀ i j, f i ≠ g j := by
    intro i j h
    have hh := congrArg Fin.val h
    change i.val = r + j.val at hh
    omega
  obtain ⟨U,V,hU,hV,hUV⟩ := tagged_frames_feasible f g hfg D
  refine ⟨fun i => (cubeBinaryEquiv n).symm (U i),
    fun j => (cubeBinaryEquiv n).symm (V j), ?_, ?_, ?_⟩
  · simpa [BinaryFrame] using hU
  · simpa [BinaryFrame] using hV
  · intro i j
    rw [character_binary_dot, Equiv.apply_symm_apply, Equiv.apply_symm_apply, hUV]

theorem sign_frames_feasible {n r s : ℕ} (hn : r+s ≤ n) (S : Fin r × Fin s → Bool) :
    ∃ (U : Fin r → Cube n) (V : Fin s → Cube n),
      BinaryFrame U ∧ BinaryFrame V ∧
      ∀ i j, character (V j) (U i) = sign (S (i,j)) := by
  obtain ⟨U,V,hU,hV,hUV⟩ := binary_frames_feasible hn (fun i j => binaryBit (S (i,j)))
  refine ⟨U,V,hU,hV,fun i j => (hUV i j).trans ?_⟩
  cases S (i,j) <;> simp [binaryBit, sign]

end Cotype

end

end OAI
