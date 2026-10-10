import Mathlib
import OAI.Combinatorics.RamseyFive.Decoding.MetadataCodec
import OAI.Combinatorics.RamseyFive.Geometry.PeelingGeometry

namespace OAI


namespace SharpRamseyFive.Metadata
open Module GreedyTraining ProjectiveTraining MeasurePublicTable
open scoped Classical LinearAlgebra.Projectivization
variable {K V J : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K] [Fintype V] [Fintype (ℙ K V)] [LinearOrder J]

theorem two_peel_message (σ g P : ℝ) (hd : finrank K V≤5)
    (hσ : 100000≤σ) (hq : Real.exp σ=Nat.card K) (hg : 0≤g) (hghi : g≤σ/2+Real.log 4)
    (H : Finset J) (hH : H.Nonempty) (Hyper : J→Submodule K V)
    (F : Finset J) (hF : F.Nonempty) (Flat : J→Submodule K V)
    (X : Finset (ℙ K V)) (hX : (X.card:ℝ)=Real.exp (2*σ+g)) :
    let XH := peelSet (P/10000<g) H hH (fun j=>flatPoints (Hyper j)) X
      ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _)
    let h := peelLength (P/10000<g) H hH (fun j=>flatPoints (Hyper j)) X
      ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _)
    let t := (Real.exp (2*σ+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-(g+σ/2)/5)
    let ht : 0<t := by positivity
    let S := peelSet (P/10000<g+σ/2) F hF (fun j=>flatPoints (Flat j)) XH ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
    let p := peelLength (P/10000<g+σ/2) F hF (fun j=>flatPoints (Flat j)) XH ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
    let raw := twoPublicOwn (greedyList H hH (fun j=>flatPoints (Hyper j)) X h)
      (greedyList F hF (fun j=>flatPoints (Flat j)) XH p)
    Real.log (Nat.card (TrainingCode V (listCap σ) (productCap σ) (Nat.card V)))≤Nat.card K ∧
    ∃c : TrainingCode V (listCap σ) (productCap σ) (Nat.card V),
      (∀x,messageOwn c x=raw x) ∧
      (∀L x,messageBase c L x=Real.exp (-L*(1-((S∩raw x).card:ℝ)/S.card))) := by
  dsimp only
  let XH := peelSet (P/10000<g) H hH (fun j=>flatPoints (Hyper j)) X
    ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _)
  let h := peelLength (P/10000<g) H hH (fun j=>flatPoints (Hyper j)) X
    ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _)
  let t := (Real.exp (2*σ+g))^(4/3:ℝ)/Real.exp σ*Real.exp (-(g+σ/2)/5)
  have ht : 0<t := by dsimp [t];positivity
  let S := peelSet (P/10000<g+σ/2) F hF (fun j=>flatPoints (Flat j)) XH ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
  let p := peelLength (P/10000<g+σ/2) F hF (fun j=>flatPoints (Flat j)) XH ⌈t⌉₊ (Nat.ceil_pos.mpr ht)
  have hc : 3*σ/2+(g+σ/2)=2*σ+g := by ring
  have hlen : (h:ℝ)*Real.exp (2*σ)≤Real.exp (3*σ/2+(g+σ/2)) := by
    have hh := peel_length_bound (P/10000<g) H hH (fun j=>flatPoints (Hyper j)) X
      ((Nat.card K)^2) (pow_pos (Nat.card_pos (α:=K)) _)
    have he : (Nat.card K:ℝ)^2=Real.exp (2*σ) := by rw [←hq,←Real.exp_nat_mul];norm_num
    rw [hc,←hX,←he]
    exact_mod_cast hh
  have plen : (p:ℝ)*Real.exp (σ+17*(g+σ/2)/15)≤Real.exp (3*σ/2+(g+σ/2)) := by
    have he : t=Real.exp (σ+17*(g+σ/2)/15) := by
      dsimp only [t]
      rw [←hc]
      exact ScoreScalars.plane_threshold_exp rfl rfl
    have hl := peel_length_real (P/10000<g+σ/2) F hF (fun j=>flatPoints (Flat j)) XH t ht
    have hphase : (p:ℝ)*Real.exp (σ+17*(g+σ/2)/15)≤XH.card := by
      calc
        _ = (p:ℝ)*t := congrArg (fun z=>(p:ℝ)*z) he.symm
        _ ≤ _ := hl
    rw [hc,←hX]
    exact hphase.trans (by exact_mod_cast Finset.card_le_card (peel_subset _ _ _ _ _ _ _))
  let Hs : Fin h→Submodule K V := fun i=>Hyper (chosen H hH (fun j=>flatPoints (Hyper j)) X i)
  let Ps : Fin p→Submodule K V := fun i=>Flat (chosen F hF (fun j=>flatPoints (Flat j)) XH i)
  obtain ⟨hcost,c,hOwn,hBase⟩ := training_message σ (g+σ/2) hd hσ hq
    (by linarith) (by linarith) hlen plen Hs Ps S
  exact ⟨hcost,c,hOwn,hBase⟩

end SharpRamseyFive.Metadata

end OAI
