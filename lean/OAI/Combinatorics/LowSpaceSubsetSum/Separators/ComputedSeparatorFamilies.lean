import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorParameterExecution
import OAI.Combinatorics.LowSpaceSubsetSum.Separators.SeparatorFamilyExecution

namespace OAI

/-! # Separator families with computed integer loop bounds

The actual family generator uses the sample size and four counts returned
by the integer preparation. Source rounded parameters only specify the
seed type and supply the correspondence proof.
-/

noncomputable section
namespace LowSpaceSubsetSum.ComputedSeparatorFamilies

variable {g n : ℕ}

structure Parameters (g : ℕ) where
  sizes : Fin 4 → ℕ
  counts : Fin 4 → ℕ
  size_le : ∀ i, sizes i ≤ g

theorem Parameters.ext {P Q : Parameters g}
    (hs : P.sizes = Q.sizes) (hc : P.counts = Q.counts) : P = Q := by
  cases P
  cases Q
  cases hs
  cases hc
  rfl

def source (S : SeparatorExpectation.RoundedParameters g) : Parameters g :=
  ⟨S.e, S.counts, S.size_le⟩

def ofData (d : SeparatorParameterExecution.Data) (h : d.size ≤ g) : Parameters g :=
  ⟨fun _ => d.size, fun i => d.counts[i.val], fun _ => h⟩

def Seed (n : ℕ) (P : Parameters g) : Type :=
  (SeparatorFamilyExecution.coupling n g 4 P.sizes P.counts P.size_le).Seed

def execute (n : ℕ) (P : Parameters g) (s : Seed n P) :=
  SeparatorFamilyExecution.run n g 4 P.sizes P.counts P.size_le s

def transport {P Q : Parameters g} (h : P = Q) (s : Seed n Q) : Seed n P := h.symm ▸ s

theorem execute_transport {P Q : Parameters g} (h : P = Q) (s : Seed n Q) :
    execute n P (transport h s) = execute n Q s := by
  subst Q
  rfl

theorem ofData_eq (S : SeparatorExpectation.RoundedParameters g)
    (d : SeparatorParameterExecution.Data) (hd : d.size ≤ g)
    (he : ∀ i, d.size = S.e i) (hc : ∀ i : Fin 4, d.counts[i.val] = S.counts i) :
    ofData d hd = source S := by
  have he' : (fun _ : Fin 4 => d.size) = S.e := funext he
  have hc' : (fun i : Fin 4 => d.counts[i.val]) = S.counts := funext hc
  exact Parameters.ext he' hc'

def draw (S : SeparatorExpectation.RoundedParameters g) (n : ℕ)
    (P : Parameters g) (h : P = source S) (s : (S.samplerCoupling n).Seed) :=
  execute n P (transport h s)

theorem draw_pair (S : SeparatorExpectation.RoundedParameters g) (n : ℕ)
    (P : Parameters g) (h : P = source S) (s : (S.samplerCoupling n).Seed) :
    draw S n P h s = SeparatorFamilyExecution.Application.run S n s :=
  execute_transport h s

def rounded (g k : ℕ) (hg : 64 ≤ g) (heven : 2 ∣ g) (hk : k ≤ g)
    (hklo : 2 * g ≤ 3 * k) : Parameters g :=
  ofData (SeparatorParameterExecution.run g k).1 (by
    rw [SeparatorParameterExecution.rounded_size g k hg heven hk hklo 0]
    exact (SeparatorParameters.rounded g k hg heven hk hklo).size_le 0)

theorem rounded_eq (g k : ℕ) (hg : 64 ≤ g) (heven : 2 ∣ g) (hk : k ≤ g)
    (hklo : 2 * g ≤ 3 * k) :
    rounded g k hg heven hk hklo = source (SeparatorParameters.rounded g k hg heven hk hklo) :=
  ofData_eq _ _ _ (SeparatorParameterExecution.rounded_size g k hg heven hk hklo)
    (SeparatorParameterExecution.rounded_counts g k hg heven hk hklo)

def run (g k n : ℕ) (hg : 64 ≤ g) (heven : 2 ∣ g) (hk : k ≤ g)
    (hklo : 2 * g ≤ 3 * k)
    (s : ((SeparatorParameters.rounded g k hg heven hk hklo).samplerCoupling n).Seed) :
    Option (Fin 4 → Array (Fin (2 ^ g))) × ℕ :=
  let prepared := SeparatorParameterExecution.run g k
  let P := ofData prepared.1 (by
    rw [SeparatorParameterExecution.rounded_size g k hg heven hk hklo 0]
    exact (SeparatorParameters.rounded g k hg heven hk hklo).size_le 0)
  let out := draw (SeparatorParameters.rounded g k hg heven hk hklo) n
    P (rounded_eq g k hg heven hk hklo) s
  (out.1, prepared.2 + out.2 + 1)

theorem value (g k n : ℕ) (hg : 64 ≤ g) (heven : 2 ∣ g) (hk : k ≤ g)
    (hklo : 2 * g ≤ 3 * k)
    (s : ((SeparatorParameters.rounded g k hg heven hk hklo).samplerCoupling n).Seed) :
    (run g k n hg heven hk hklo s).1 =
      (SeparatorFamilyExecution.Application.run (SeparatorParameters.rounded g k hg heven hk hklo) n s).1 := by
  change (draw _ n _ _ s).1 = _
  exact congrArg Prod.fst (draw_pair _ _ _ _ s)

theorem work (g k n : ℕ) (hg : 64 ≤ g) (heven : 2 ∣ g) (hk : k ≤ g)
    (hklo : 2 * g ≤ 3 * k)
    (s : ((SeparatorParameters.rounded g k hg heven hk hklo).samplerCoupling n).Seed) :
    (run g k n hg heven hk hklo s).2 ≤
      60 * g + 51 + 44 * 2 ^ g * (g * n ^ 3 + 32 * (g + 1) ^ 3 + 4) + 22 := by
  have hp := SeparatorParameterExecution.work g k
  have hf := SeparatorFamilyExecution.Application.work
    (SeparatorParameters.rounded g k hg heven hk hklo) n s
  have he := congrArg Prod.snd (draw_pair (SeparatorParameters.rounded g k hg heven hk hklo)
    n (rounded g k hg heven hk hklo) (rounded_eq g k hg heven hk hklo) s)
  dsimp only [rounded] at he
  change _ + _ + 1 ≤ _
  rw [he]
  omega

end LowSpaceSubsetSum.ComputedSeparatorFamilies

end

end OAI
