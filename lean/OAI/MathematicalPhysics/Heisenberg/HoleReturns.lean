import OAI.MathematicalPhysics.Heisenberg.ClockTails

namespace OAI

section
noncomputable section
open scoped Classical
open Matrix
noncomputable section
open scoped Classical
open Matrix
noncomputable section
open scoped Classical
open Matrix
noncomputable section
open scoped Classical
noncomputable section
open scoped BigOperators Classical
noncomputable section
open scoped Classical

namespace Heisenberg.Exposure
variable {T : Type*} [Fintype T]

end Heisenberg.Exposure

namespace Heisenberg.Exposure
open Heisenberg.Cycle Heisenberg.LayeredExchange
variable {T V : Type*} [Fintype T] [Fintype V]

end Heisenberg.Exposure

namespace Heisenberg.Exposure
open LayeredExchange Heisenberg.Cycle
variable {V : Type*} [Fintype V] [DecidableEq V]

attribute [local irreducible] MissingSet layerHistory

end Heisenberg.Exposure

namespace Heisenberg.Exposure
open Heisenberg.Cycle LayeredExchange
variable {V W : Type*}

variable [Fintype V] [DecidableEq V]

end Heisenberg.Exposure

namespace Heisenberg.Hitting
open Filter
variable {V : Type*} [Fintype V]

variable [DecidableEq V]

end Heisenberg.Hitting
namespace Heisenberg.Exposure
variable {J Q : Type*} [Fintype J] [Fintype Q] [DecidableEq J] [DecidableEq Q]
end Heisenberg.Exposure

namespace Heisenberg.Exposure
variable {J Q Ω : Type*} [Fintype J] [Fintype Q] [Fintype Ω]
  [DecidableEq J] [DecidableEq Q]

end Heisenberg.Exposure

namespace Heisenberg.Exposure
open Matrix
variable {V Ω : Type*} [Fintype V] [Fintype Ω] [DecidableEq V]

end Heisenberg.Exposure

noncomputable section
open scoped Classical
open Filter
namespace Heisenberg.Hitting

variable {V : Type*} [Fintype V]

end Heisenberg.Hitting

namespace Heisenberg.Exposure
open Matrix Heisenberg.Hitting
variable {V Ω : Type*} [Fintype V] [DecidableEq V] [Fintype Ω]

end Heisenberg.Exposure

noncomputable section
open scoped Classical
namespace Heisenberg.Return
open Equiv
variable {V : Type*}

variable [Fintype V]

end Heisenberg.Return

namespace Heisenberg.Exposure
open Heisenberg.Return
variable {V : Type*} [Fintype V]

end Heisenberg.Exposure

noncomputable section
open scoped Classical
namespace Heisenberg.Conditioning
variable {Ω : Type*} [Fintype Ω]

end Heisenberg.Conditioning

attribute [local instance] exposureDecEq
namespace Heisenberg.Exposure
open Heisenberg.Cycle Heisenberg.Conditioning
variable {V : Type*} [Fintype V]

end Heisenberg.Exposure
attribute [-instance] exposureDecEq

namespace Heisenberg.Exposure
open Heisenberg.Return Heisenberg.Hitting Heisenberg.Cycle
variable {V Ω : Type*} [Fintype V] [Fintype Ω]
variable [DecidableEq V]

def holePinEquiv (A P : Set V) (hP : Disjoint A P) :
    {x : {z : V // z∉A} // x.val∈P} ≃ P where
  toFun j := ⟨j.val.val,j.property⟩
  invFun j := ⟨⟨j.val,fun h => Set.disjoint_left.mp hP h j.property⟩,j.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

def returnCount (σ : Equiv.Perm V) (P : Set V) (T : Finset P) : ℝ :=
  ∑ j∈T, if nextPermutation σ P j∈T then 1 else 0

lemma returnCount_split (σ : Equiv.Perm V) (A P : Set V)
    (hA : ∀ x,σ x∉A ↔ x∉A) (hP : Disjoint A P)
    (hh : AllHit (splitHolePerm σ A P hA)) (T : Finset P) :
    let H := T.map (holePinEquiv A P hP).symm.toEmbedding
    (∑ j∈H,if nextPin (splitHolePerm σ A P hA) hh j∈H then (1:ℝ) else 0) =
      returnCount σ P T := by
  dsimp only
  rw [Finset.sum_map]
  apply Finset.sum_congr rfl
  intro j _
  have he : nextPin (splitHolePerm σ A P hA) hh ((holePinEquiv A P hP).symm j) =
      (holePinEquiv A P hP).symm (nextPermutation σ P j) := by
    apply Subtype.ext
    apply Subtype.ext
    exact split_nextPin_eq σ A P hA hP hh _
  simp only [Equiv.toEmbedding_apply,he,Finset.mem_map_equiv,Equiv.symm_symm,Equiv.apply_symm_apply]

omit [Fintype V] in
lemma holePins_image (A P : Set V) (hP : Disjoint A P) (T : Finset P) :
    (T.map (holePinEquiv A P hP).symm.toEmbedding).image (fun j => j.val.val) =
      T.image (fun j => j.val) := by
  rw [Finset.map_eq_image,Finset.image_image]
  rfl

theorem outside_return_energy (μ : Ω → ℝ) (hμ : ∀ c,0≤μ c) (hs : ∑ c,μ c=1)
    (σ : Ω → Equiv.Perm V) (A P D : Set V)
    (hA : ∀ c x,σ c x∉A ↔ x∉A) (hP : Disjoint A P)
    (hd : DeterminantLaw μ (fun c => (σ c).permMatrix ℝ |>.transpose))
    (hz : (∑ c,if OutsideHit (σ c) P A then μ c else 0)≠0)
    (T : Finset P) (hT : ∀ j∈T,j.val∈D) (hQ : Aᶜ∩Pᶜ ⊆ D) :
    (∑ c,if OutsideHit (σ c) P A then μ c*returnCount (σ c) P T else 0) /
      (∑ c,if OutsideHit (σ c) P A then μ c else 0) ≤
      (T.card:ℝ)-energy (killedMean μ σ D) (hitting (killedMean μ σ D) (T.image Subtype.val)) := by
  let H := T.map (holePinEquiv A P hP).symm.toEmbedding
  have hz' : hitWeight μ (fun c => splitHolePerm (σ c) A P (hA c)) ≠ 0 := by
    simpa only [hitWeight,allHit_splitHolePerm _ _ _ _ hP] using hz
  have hH : ∀ j∈H,j.val.val∈D := by
    intro j hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hj
    exact hT i hi
  have h := split_conditional_return_energy μ hμ hs σ A P D hA hd hz' H hH hQ
  dsimp only at h
  rw [show H.card=T.card from Finset.card_map _,holePins_image A P hP T] at h
  convert h using 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : OutsideHit (σ c) P A
  · have hh := (allHit_splitHolePerm (σ c) A P (hA c) hP).mpr hc
    rw [ite_eq_left hc,dite_eq_left hh,returnCount_split (σ c) A P (hA c) hP hh T]
    unfold hitWeight
    simp only [allHit_splitHolePerm _ _ _ _ hP]
    ring
  · rw [ite_eq_right hc,dite_eq_right (fun h => hc ((allHit_splitHolePerm _ _ _ _ hP).mp h))]
    exact zero_div _

end Heisenberg.Exposure

namespace Heisenberg.Exposure
attribute [local irreducible] killedMean Heisenberg.Hitting.hitting Heisenberg.Hitting.energy Heisenberg.Cycle.MissingSet layerHistory
open Heisenberg.Return Heisenberg.Hitting Heisenberg.Cycle Heisenberg.Conditioning
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem exposed_layer_energy {n : ℕ} (s : Equiv.Perm (Fin n)) (a b : Fin n → V)
    (p : Fin n → ℝ) (hp : ∀ i,0≤p i ∧ p i≤1) (P : Set (Fin n×V))
    (base : Fin n → Bool)
    (hbase : productWeight (fun i z => if z then p i else 1-p i) base≠0)
    (D : Set (Fin n×V)) (T : Finset P)
    (hT : ∀ j∈T,j.val∈D)
    (hQ : (MissingSet (layerHistory s (fun i => Equiv.swap (a i) (b i)) base) P)ᶜ∩Pᶜ ⊆ D) :
    let τ := fun i => Equiv.swap (a i) (b i)
    let μ₀ := productWeight (fun i z => if z then p i else 1-p i)
    let μ := fun c => μ₀ c*(2:ℝ)^missingCount (layerHistory s τ c) P
    let M := layerRevealed τ (MissingSet (layerHistory s τ base) P)
    let σ := fun c => layerHistory s τ (residualCoins M base c)
    conditional μ (layerExposure s τ P) (fun c => returnCount (layerHistory s τ c) P T) base ≤
      (T.card:ℝ)-energy (killedMean μ₀ σ D) (hitting (killedMean μ₀ σ D) (T.image Subtype.val)) := by
  dsimp only
  let τ := fun i => Equiv.swap (a i) (b i)
  let w : Fin n → Bool → ℝ := fun i z => if z then p i else 1-p i
  have hw : ∀ i,∑ z,w i z=1 := by intro i; simp [w]
  have hw0 : ∀ i z,0≤w i z := by
    intro i z
    cases z <;> simp only [w,Bool.false_eq_true,↓reduceIte] <;> linarith [(hp i).1,(hp i).2]
  let A := MissingSet (layerHistory s τ base) P
  let M := layerRevealed τ A
  let σ := fun c => layerHistory s τ (residualCoins M base c)
  have hσ : σ base=layerHistory s τ base := by
    change layerHistory s τ (residualCoins M base base)=layerHistory s τ base
    apply congrArg (layerHistory s τ)
    funext i
    simp only [residualCoins,ite_self]
  have ho : OutsideHit (σ base) P A := by
    rw [hσ]
    exact (sameMissing_iff_outsideHit _ _ P (fun _ _ => rfl)).mp rfl
  have hμ : ∀ c,0≤productWeight w c := productWeight_nonneg w hw0
  have hz : (∑ c : Fin n → Bool,if OutsideHit (σ c) P A then productWeight w c else 0)≠0 := by
    apply ne_of_gt
    have hb : 0<productWeight w base := lt_of_le_of_ne (hμ base) (Ne.symm hbase)
    exact lt_of_lt_of_le hb (by
      have he : productWeight w base=(if OutsideHit (σ base) P A then productWeight w base else 0) := (ite_eq_left ho).symm
      rw [he]
      apply Finset.single_le_sum _ (Finset.mem_univ base)
      intro c _
      split_ifs
      · exact hμ c
      · exact le_rfl)
  rw [conditional_layer_exposure s τ w hw hw0 P base _ hbase]
  have hs : (∑ c : Fin n → Bool,productWeight w c)=1 := by
    convert productWeight_sum w hw using 1
    congr 1
    ext c
    simp
  have hd : DeterminantLaw (productWeight w)
      (fun c => (σ c).permMatrix ℝ |>.transpose) := by
    exact residual_determinantLaw s a b P base p
  have hh := outside_return_energy (productWeight w) hμ hs σ A P D
    (fun c => residual_invariant s τ P base c) (missing_disjoint_pins _ P) hd hz T hT hQ
  exact hh

end Heisenberg.Exposure
end
end
end
end
end
end
end
end
end
end

end OAI
