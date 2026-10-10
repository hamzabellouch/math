import OAI.GroupTheory.PolycyclicRecognition.Finiteness.NormalInductionDimension
import Mathlib.Algebra.Homology.HomotopyCofiber
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

namespace OAI

/-! # Coordinates on the mapping cone used for cyclic extensions -/

noncomputable section
namespace PolycyclicRecognition

open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance 2000] Rep.hV2

variable {k G : Type} [CommRing k] [Group G]

theorem rep_shortComplex_exact_iff (S : ShortComplex (Rep k G)) :
    S.Exact ↔ ∀ x : S.X₂, S.g.hom x = 0 → ∃ y : S.X₁, S.f.hom y = x := by
  constructor
  · intro h
    exact (ShortComplex.moduleCat_exact_iff _).mp
      (h.map (forget₂ (Rep k G) (ModuleCat k)))
  · intro h
    apply (forget₂ (Rep k G) (ModuleCat k)).reflects_exact_of_faithful
    exact (ShortComplex.moduleCat_exact_iff _).mpr h

variable {P Q : ChainComplex (Rep k G) ℕ} (φ : P ⟶ Q)

abbrev repCofiber := homotopyCofiber φ
abbrev repCofiberFst (i : ℕ) : (repCofiber φ).X (i + 1) ⟶ P.X i :=
  homotopyCofiber.fstX φ (i + 1) i (by rfl)
abbrev repCofiberSnd (i : ℕ) : (repCofiber φ).X i ⟶ Q.X i :=
  homotopyCofiber.sndX φ i
abbrev repCofiberInl (i : ℕ) : P.X i ⟶ (repCofiber φ).X (i + 1) :=
  homotopyCofiber.inlX φ i (i + 1) (by rfl)
abbrev repCofiberInr (i : ℕ) : Q.X i ⟶ (repCofiber φ).X i :=
  homotopyCofiber.inrX φ i

theorem repCofiber_zero_decompose (x : (repCofiber φ).X 0) :
    (repCofiberInr φ 0).hom ((repCofiberSnd φ 0).hom x) = x :=
  congrArg (fun f => f.hom x) (homotopyCofiber.sndX_inrX φ 0 (by simp))

theorem repCofiber_ext_zero {x y : (repCofiber φ).X 0}
    (h : (repCofiberSnd φ 0).hom x = (repCofiberSnd φ 0).hom y) : x = y := by
  rw [← repCofiber_zero_decompose φ x, ← repCofiber_zero_decompose φ y, h]

theorem repCofiber_decompose (i : ℕ) (x : (repCofiber φ).X (i + 1)) :
    (repCofiberInl φ i).hom ((repCofiberFst φ i).hom x) +
      (repCofiberInr φ (i + 1)).hom ((repCofiberSnd φ (i + 1)).hom x) = x := by
  have h : repCofiberFst φ i ≫ repCofiberInl φ i +
      repCofiberSnd φ (i + 1) ≫ repCofiberInr φ (i + 1) = 𝟙 _ := by
    apply homotopyCofiber.ext_to_X φ (i + 1) i (by rfl)
    · simp only [Preadditive.add_comp, Category.assoc, Category.id_comp]
      rw [homotopyCofiber.inlX_fstX φ i (i + 1) (by rfl),
        homotopyCofiber.inrX_fstX φ (i + 1) i (by rfl)]
      simp
    · simp only [Preadditive.add_comp, Category.assoc, Category.id_comp]
      rw [homotopyCofiber.inlX_sndX φ i (i + 1) (by rfl),
        homotopyCofiber.inrX_sndX φ (i + 1)]
      simp
  exact congrArg (fun f => f.hom x) h

theorem repCofiber_snd_d (i : ℕ) (x : (repCofiber φ).X (i + 1)) :
    (repCofiberSnd φ i).hom (((repCofiber φ).d (i + 1) i).hom x) =
      (φ.f i).hom ((repCofiberFst φ i).hom x) +
        (Q.d (i + 1) i).hom ((repCofiberSnd φ (i + 1)).hom x) := by
  exact congrArg (fun f => f.hom x) (homotopyCofiber.d_sndX φ (i + 1) i (by rfl))

theorem repCofiber_fst_d (i : ℕ) (x : (repCofiber φ).X (i + 2)) :
    (repCofiberFst φ i).hom (((repCofiber φ).d (i + 2) (i + 1)).hom x) =
      -(P.d (i + 1) i).hom ((repCofiberFst φ (i + 1)).hom x) := by
  exact congrArg (fun f => f.hom x)
    (homotopyCofiber.d_fstX φ (i + 2) (i + 1) i (by rfl) (by rfl))

theorem repCofiber_fst_inl (i : ℕ) (x : P.X i) :
    (repCofiberFst φ i).hom ((repCofiberInl φ i).hom x) = x :=
  congrArg (fun f => f.hom x) (homotopyCofiber.inlX_fstX φ i (i + 1) (by rfl))

theorem repCofiber_snd_inl (i : ℕ) (x : P.X i) :
    (repCofiberSnd φ (i + 1)).hom ((repCofiberInl φ i).hom x) = 0 :=
  congrArg (fun f => f.hom x) (homotopyCofiber.inlX_sndX φ i (i + 1) (by rfl))

theorem repCofiber_fst_inr (i : ℕ) (x : Q.X (i + 1)) :
    (repCofiberFst φ i).hom ((repCofiberInr φ (i + 1)).hom x) = 0 :=
  congrArg (fun f => f.hom x) (homotopyCofiber.inrX_fstX φ (i + 1) i (by rfl))

theorem repCofiber_snd_inr (i : ℕ) (x : Q.X i) :
    (repCofiberSnd φ i).hom ((repCofiberInr φ i).hom x) = x :=
  congrArg (fun f => f.hom x) (homotopyCofiber.inrX_sndX φ i)

theorem repCofiber_ext (i : ℕ) {x y : (repCofiber φ).X (i + 1)}
    (h₁ : (repCofiberFst φ i).hom x = (repCofiberFst φ i).hom y)
    (h₂ : (repCofiberSnd φ (i + 1)).hom x = (repCofiberSnd φ (i + 1)).hom y) : x = y := by
  rw [← repCofiber_decompose φ i x, ← repCofiber_decompose φ i y, h₁, h₂]

end PolycyclicRecognition

end

end OAI
