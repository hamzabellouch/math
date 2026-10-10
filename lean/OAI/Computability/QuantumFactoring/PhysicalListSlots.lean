import Mathlib
import OAI.Computability.QuantumFactoring.TensorPreparation
import OAI.Computability.QuantumFactoring.TransitionWords
import OAI.Computability.QuantumFactoring.ListSamplerCircuit

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators


namespace ExactQuantumFactoring
open scoped BigOperators
open Exactness RepeatedTrials
namespace PhysicalListSlots

abbrev ordinaryWidth (n : ℕ) := tensorWidth (ListSampler.width n) (n^5)
abbrev Result (n : ℕ) := Completion.Raw (Basis (ordinaryWidth n))
  (Completion.transitionWidth n) (2*n) (n*n^5)
noncomputable instance resultFintype (n : ℕ) : Fintype (Result n) := inferInstance

def sampleRead {n : ℕ} (x : Basis (ListSampler.width n)) : Basis n := fun i =>
  x ⟨n+n+i.val,by have := i.isLt; dsimp [ListSampler.width]; omega⟩
lemma sampleRead_word {n : ℕ} (m mask y : Basis n) : sampleRead (ListSampler.word m mask y)=y := by
  funext i
  exact ListSampler.word_sample _ _ _ _

def ordinary {n : ℕ} (x : Basis (ordinaryWidth n)) : Basis (Completion.transitionWidth n) :=
  TransitionWords.encode (fun i => sampleRead ((tensorLayout _ (n^5)).symm x i))

def ordinaryProgram (n : ℕ) : List (Instruction (ordinaryWidth n)) :=
  tensorProgram (ListSampler.circuit n) (n^5)

def ordinaryZero {n : ℕ} (m : Basis n) : Basis (ordinaryWidth n) :=
  tensorLayout _ (n^5) (fun _ => ListSampler.word m (fun _ => false) (fun _ => false))

noncomputable def ordinaryState {n : ℕ} (m : Basis n) : State (ordinaryWidth n) :=
  (programMatrix (ordinaryProgram n)).mulVec (basisVector (ordinaryZero m))

lemma single_normalized {n : ℕ} (m : Basis n) :
    ∑ x,Complex.normSq ((programMatrix (ListSampler.circuit n)).mulVec
      (basisVector (ListSampler.word m (fun _ => false) (fun _ => false))) x)=1 := by
  have hh := ListSampler.circuit_mass n m (fun _ => True)
  simp only [outcomeMass,ite_true] at hh
  exact hh.trans (fairState_normalized _)

lemma ordinary_normalized {n : ℕ} (m : Basis n) : ∑ x,Complex.normSq (ordinaryState m x)=1 := by
  have hh := tensorProgram_event (ListSampler.circuit n) (n^5)
    (ListSampler.word m (fun _ => false) (fun _ => false)) (fun _ => True)
  change outcomeMass (fun _ => True) (ordinaryState m)=_ at hh
  simp only [outcomeMass,ite_true] at hh
  exact hh.trans (tensor_normalized _ _ (single_normalized m))

lemma ordinary_good_mass {n : ℕ} (m : Basis n) (hm : (bitsValue m).toNat≠0)
    (hodd : Odd (bitsValue m).toNat) (p₀ : Component (bitsValue m).toNat) :
    outcomeMass (ListSlots.GoodOutput hm (bitsValue m).isLt p₀ ∘ ordinary) (ordinaryState m)=
      (Completion.listSuccess (bitsValue m).toNat n (n^5):ℝ) := by
  have he : ListSlots.GoodOutput hm (bitsValue m).isLt p₀ ∘ ordinary =
      (fun x : Fin (n^5)→Basis (ListSampler.width n) => ∃ i,
        FavorableBits hm (bitsValue m).isLt p₀ n (sampleRead (x i))) ∘ (tensorLayout _ (n^5)).symm := by
    funext x
    apply propext
    simp only [Function.comp_def,ListSlots.GoodOutput,ordinary,TransitionWords.read_encode,FavorableBits]
    exact ⟨fun ⟨i,u,h,hf⟩ => ⟨i,u,h.symm,hf⟩,fun ⟨i,u,h,hf⟩ => ⟨i,u,h.symm,hf⟩⟩
  rw [he,ordinaryState,ordinaryProgram,ordinaryZero,tensorProgram_event]
  rw [tensor_some_mass _ _ (fun x => FavorableBits hm (bitsValue m).isLt p₀ n (sampleRead x)) (single_normalized m)]
  rw [ListSampler.circuit_mass]
  have hs : (fun y => FavorableBits hm (bitsValue m).isLt p₀ n
      (sampleRead (ListSampler.word m ((listMaskNet n).eval m)
        (padBits (Nat.clog_le_of_le_pow (bitsValue m).isLt.le) y)))) =
      FavorableBits hm (bitsValue m).isLt p₀ (Nat.clog 2 (bitsValue m).toNat) := by
    funext y
    simp only [sampleRead_word,FavorableBits,padBits_value]
  rw [hs,favorableBits_mass hm (bitsValue m).isLt hodd p₀ (Nat.le_pow_clog (by decide) _)]
  simp only [Completion.listSuccess,Rat.cast_sub,Rat.cast_one,Rat.cast_pow,Rat.cast_div,
    Rat.cast_natCast,Rat.cast_ofNat]

noncomputable def fresh {n : ℕ} (m : Basis n) : Result n→ℂ :=
  Completion.fresh (ordinaryState m) (Completion.transitionWidth n) (2*n) (n*n^5)
noncomputable def passed {n : ℕ} (m : Basis n) (hm : (bitsValue m).toNat≠0)
    (p₀ : Component (bitsValue m).toNat) : Result n→Prop :=
  Completion.passed (ListSlots.GoodOutput hm (bitsValue m).isLt p₀ ∘ ordinary)
    (ListSlots.canonical hm (bitsValue m).isLt p₀)
    (Completion.listSuccess (bitsValue m).toNat n (n^5)) (Completion.target n)
def output {n : ℕ} : Result n→Basis (Completion.transitionWidth n) := Completion.output ordinary

lemma fresh_normalized {n : ℕ} (m : Basis n) : ∑ r,Complex.normSq (fresh m r)=1 :=
  Completion.fresh_normalized _ _ _ _ (ordinary_normalized m)

lemma passed_mass {n : ℕ} (hn : 128 ≤ n) (m : Basis n) (hm : 2 ≤ (bitsValue m).toNat)
    (hodd : Odd (bitsValue m).toNat) (p₀ p₁ : Component (bitsValue m).toNat) (hne : p₁≠p₀) :
    outcomeMass (passed m (by omega) p₀) (fresh m)=(Completion.target n:ℝ) := by
  have hl := Completion.listSuccess_lower hn hm (bitsValue m).isLt hodd p₀ p₁ hne
  have hu := Completion.listSuccess_le_one (by omega) (bitsValue m).isLt hodd p₀ (n^5)
  have hε : (1:ℚ)/(2:ℚ)^(2*n)<1 := by
    apply (div_lt_one (by positivity)).mpr
    exact one_lt_pow₀ (by norm_num) (by omega)
  apply Completion.passed_mass _ _ _ _ _ (ordinary_normalized m)
    (ordinary_good_mass m (by omega) hodd p₀)
    (Completion.listSuccess_at (bitsValue m).isLt.le _) (Completion.target_at n)
  · unfold Completion.coinBits Completion.transitionWidth; omega
  · linarith
  · exact hu
  · omega
  · exact Completion.target_pos (by omega)
  · exact Completion.target_le_ordinary (by omega) hl

lemma passed_good {n : ℕ} (hn : 128 ≤ n) (m : Basis n) (hm : (bitsValue m).toNat≠0)
    (hodd : Odd (bitsValue m).toNat) (p₀ p₁ : Component (bitsValue m).toNat) (hne : p₁≠p₀)
    (r : Result n) (hp : passed m hm p₀ r) : ListSlots.GoodOutput hm (bitsValue m).isLt p₀ (output r) :=
  Completion.passed_good ordinary _ _ _ _
    (ListSlots.canonical_good hn hm (bitsValue m).isLt hodd p₀ p₁ hne) r hp

abbrev width (n : ℕ) := 2*n+(ordinaryWidth n+(Completion.transitionWidth n+
  Completion.coinBits (Completion.transitionWidth n) (2*n) (n*n^5)))
def layout (n : ℕ) : Result n≃Basis (width n) := Completion.layout _ _ _ _
def program (n : ℕ) : List (Instruction (width n)) :=
  Completion.program (ordinaryProgram n) (Completion.transitionWidth n) (2*n) (n*n^5)
def zero {n : ℕ} (m : Basis n) : Result n :=
  ((fun _ => false),ordinaryZero m,(fun _ => false),(fun _ => false))

lemma program_entry {n : ℕ} (m : Basis n) (r : Result n) :
    (programMatrix (program n)).mulVec (basisVector (layout n (zero m))) (layout n r)=fresh m r :=
  Completion.program_entry _ _ _ _ _ _
lemma program_state {n : ℕ} (m : Basis n) :
    (programMatrix (program n)).mulVec (basisVector (layout n (zero m)))=encodeState (layout n) (fresh m) := by
  funext x
  obtain ⟨r,rfl⟩ := (layout n).surjective x
  rw [program_entry,encodeState_at _ (layout n).injective]

lemma program_length (n : ℕ) : (program n).length ≤
    n^5*(4*ListSampler.work n+3*n)+2*n+Completion.transitionWidth n+
      Completion.coinBits (Completion.transitionWidth n) (2*n) (n*n^5) := by
  rw [program,Completion.program_length,ordinaryProgram,tensorProgram_length]
  have hh := Nat.mul_le_mul_left (n^5) (ListSampler.circuit_length n)
  omega

end PhysicalListSlots
end ExactQuantumFactoring


end

end OAI
