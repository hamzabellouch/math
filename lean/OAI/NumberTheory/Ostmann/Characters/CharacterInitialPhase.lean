import OAI.NumberTheory.Ostmann.Characters.CharacterPoisson

namespace OAI

noncomputable section
open scoped BigOperators FourierTransform
namespace Ostmann.Characters
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def initialUnary (p:ι→ℕ) [∀i,Fact (p i).Prime]
    (χ:∀i,MulChar (ZMod (p i)) ℂ) (a:∀i,ZMod (p i)) (s:ℤ) (i:ι) : ℂ :=
  (gaussSum (χ i) ZMod.stdAddChar/(Real.sqrt (p i):ℂ))*
    ZMod.stdAddChar (-(a i*Construction.crtFrequency p s i))*(χ i)⁻¹ (-(s:ZMod (p i)))

def initialPhase (p:ι→ℕ) [∀i,Fact (p i).Prime]
    (χ:∀i,MulChar (ZMod (p i)) ℂ) (a:∀i,ZMod (p i)) (s:ℤ) : ℂ :=
  ∏i,initialUnary p χ a s i * ∏j∈Finset.univ.erase i,χ i (p j:ZMod (p i))

theorem characterAmplitude_crt (p:ι→ℕ) [∀i,Fact (p i).Prime]
    (χ:∀i,MulChar (ZMod (p i)) ℂ) (a:∀i,ZMod (p i)) (s:ℤ) (i:ι) :
    characterAmplitude (χ i) (a i) (Construction.crtFrequency p s i) =
      initialUnary p χ a s i * ∏j∈Finset.univ.erase i,χ i (p j:ZMod (p i)) := by
  have he : -(Construction.crtFrequency p s i)=
      (-(s:ZMod (p i)))*(Construction.otherProduct p i:ZMod (p i))⁻¹ := by
    unfold Construction.crtFrequency
    ring
  have hi : (χ i)⁻¹ ((Construction.otherProduct p i:ZMod (p i))⁻¹)=
      χ i (Construction.otherProduct p i:ZMod (p i)) := by
    rw [MulChar.inv_apply',inv_inv]
  have hp : χ i (Construction.otherProduct p i:ZMod (p i))=
      ∏j∈Finset.univ.erase i,χ i (p j:ZMod (p i)) := by
    simp only [Construction.otherProduct,Nat.cast_prod,map_prod]
  unfold characterAmplitude initialUnary
  rw [he,map_mul,hi,hp]
  ring

theorem initial_character_poisson (p:ι→ℕ) [∀i,Fact (p i).Prime] [NeZero (∏i,p i)]
    (hcop:Pairwise (fun i j=>(p i).Coprime (p j)))
    (χ:∀i,MulChar (ZMod (p i)) ℂ) (hχ:∀i,χ i≠1)
    (a:∀i,ZMod (p i)) (ψ:SchwartzMap ℝ ℂ) {X:ℝ} (hX:0<X) :
    (∑' n:ℤ,(∏i,χ i ((n:ZMod (p i))-a i))*ψ ((n:ℝ)/X))/(Real.sqrt X:ℂ) =
      (Real.sqrt (X/(∏i,p i:ℕ)):ℂ)*
        (∑' s:ℤ,initialPhase p χ a s*𝓕 ψ (-(s:ℝ)*X/(∏i,p i:ℕ))) := by
  rw [character_normalized_poisson p hcop χ hχ a ψ hX]
  simp_rw [characterAmplitude_crt]
  rfl

end Ostmann.Characters

end

end OAI
