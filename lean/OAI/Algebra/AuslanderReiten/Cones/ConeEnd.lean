import OAI.Algebra.AuslanderReiten.HomComplex.FullHomProducts
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

namespace OAI

noncomputable section

namespace ArExplicit

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CochainComplex CochainComplex.HomComplex
open CochainComplex.mappingCone

variable {C : Type*} [Category* C] [Preadditive C]
variable {F G : CochainComplex C ℤ} (φ : F ⟶ G) [HasHomotopyCofiber φ]
variable {n : ℤ}

def coneEnd (a : Cochain G G n) (b : Cochain F F n) (c : Cochain F G (n - 1)) :
    Cochain (mappingCone φ) (mappingCone φ) n :=
  descCochain φ (liftCochain φ b c (by omega))
    (liftCochain φ (0 : Cochain G F (n + 1)) a rfl) (by omega)

def coneEndA (x : Cochain (mappingCone φ) (mappingCone φ) n) : Cochain G G n :=
  ((Cochain.ofHom (inr φ)).comp x (zero_add n)).comp (snd φ) (add_zero n)

def coneEndB (x : Cochain (mappingCone φ) (mappingCone φ) n) : Cochain F F n :=
  ((inl φ).comp x (show -1 + n = n - 1 by omega)).comp (fst φ).1 (by omega)

def coneEndC (x : Cochain (mappingCone φ) (mappingCone φ) n) : Cochain F G (n - 1) :=
  ((inl φ).comp x (show -1 + n = n - 1 by omega)).comp (snd φ) (add_zero _)

def coneEndUpper (x : Cochain (mappingCone φ) (mappingCone φ) n) : Cochain G F (n + 1) :=
  ((Cochain.ofHom (inr φ)).comp x (zero_add n)).comp (fst φ).1 rfl

@[simp] theorem coneEndA_mk (a : Cochain G G n) (b : Cochain F F n)
    (c : Cochain F G (n - 1)) : coneEndA φ (coneEnd φ a b c) = a := by
  simp [coneEndA, coneEnd]

@[simp] theorem coneEndB_mk (a : Cochain G G n) (b : Cochain F F n)
    (c : Cochain F G (n - 1)) : coneEndB φ (coneEnd φ a b c) = b := by
  simp [coneEndB, coneEnd]

@[simp] theorem coneEndC_mk (a : Cochain G G n) (b : Cochain F F n)
    (c : Cochain F G (n - 1)) : coneEndC φ (coneEnd φ a b c) = c := by
  simp [coneEndC, coneEnd]

@[simp] theorem coneEndUpper_mk (a : Cochain G G n) (b : Cochain F F n)
    (c : Cochain F G (n - 1)) : coneEndUpper φ (coneEnd φ a b c) = 0 := by
  simp [coneEndUpper, coneEnd]

theorem coneEnd_ext {x y : Cochain (mappingCone φ) (mappingCone φ) n}
    (ha : coneEndA φ x = coneEndA φ y) (hb : coneEndB φ x = coneEndB φ y)
    (hc : coneEndC φ x = coneEndC φ y) (hu : coneEndUpper φ x = coneEndUpper φ y) : x = y := by
  apply (ext_cochain_from_iff φ (n - 1) n (by omega)).mpr
  constructor
  · exact (ext_cochain_to_iff φ (n - 1) n (by omega)).mpr ⟨hb, hc⟩
  · exact (ext_cochain_to_iff φ n (n + 1) rfl).mpr ⟨hu, ha⟩

theorem coneEnd_reconstruct (x : Cochain (mappingCone φ) (mappingCone φ) n)
    (hu : coneEndUpper φ x = 0) :
    coneEnd φ (coneEndA φ x) (coneEndB φ x) (coneEndC φ x) = x := by
  apply coneEnd_ext φ <;> simp [hu]

@[simp] theorem coneEnd_zero :
    coneEnd φ (0 : Cochain G G n) (0 : Cochain F F n) (0 : Cochain F G (n - 1)) = 0 := by
  simp [coneEnd, descCochain, liftCochain]

theorem coneEnd_eq_zero_iff (a : Cochain G G n) (b : Cochain F F n)
    (c : Cochain F G (n - 1)) : coneEnd φ a b c = 0 ↔ a = 0 ∧ b = 0 ∧ c = 0 := by
  constructor
  · intro h
    have ha := congrArg (coneEndA φ) h
    have hb := congrArg (coneEndB φ) h
    have hc := congrArg (coneEndC φ) h
    rw [coneEndA_mk] at ha
    rw [coneEndB_mk] at hb
    rw [coneEndC_mk] at hc
    exact ⟨ha.trans (by simp [coneEndA]), hb.trans (by simp [coneEndB]),
      hc.trans (by simp [coneEndC])⟩
  · rintro ⟨rfl, rfl, rfl⟩
    exact coneEnd_zero φ

theorem coneEnd_differential (a : Cochain G G n) (b : Cochain F F n)
    (c : Cochain F G (n - 1)) :
    δ n (n + 1) (coneEnd φ a b c) =
      descCochain φ
        (liftCochain φ (-(δ n (n + 1) b))
          (δ (n - 1) n c + b.comp (Cochain.ofHom φ) (add_zero n) +
            (n + 1).negOnePow • (Cochain.ofHom φ).comp a (zero_add n)) rfl)
        (liftCochain φ (0 : Cochain G F ((n + 1) + 1)) (δ n (n + 1) a) rfl) rfl := by
  rw [coneEnd, δ_descCochain φ _ _ (by omega) (n + 1) rfl,
    δ_liftCochain φ _ _ (by omega) (n + 1) rfl,
    δ_liftCochain φ _ _ rfl ((n + 1) + 1) rfl]
  apply (ext_cochain_from_iff φ n (n + 1) rfl).mpr
  constructor
  · apply (ext_cochain_to_iff φ n (n + 1) rfl).mpr
    constructor <;> simp [liftCochain, descCochain]
  · apply (ext_cochain_to_iff φ (n + 1) ((n + 1) + 1) rfl).mpr
    constructor <;> simp [liftCochain, descCochain]

theorem coneEnd_closed_iff (a : Cochain G G n) (b : Cochain F F n)
    (c : Cochain F G (n - 1)) :
    δ n (n + 1) (coneEnd φ a b c) = 0 ↔
      δ n (n + 1) a = 0 ∧ δ n (n + 1) b = 0 ∧
        δ (n - 1) n c + b.comp (Cochain.ofHom φ) (add_zero n) +
          (n + 1).negOnePow • (Cochain.ofHom φ).comp a (zero_add n) = 0 := by
  rw [coneEnd_differential]
  rw [ext_cochain_from_iff φ n (n + 1) rfl]
  simp only [Cochain.comp_zero, inl_descCochain, inr_descCochain]
  rw [ext_cochain_to_iff φ n (n + 1) rfl,
    ext_cochain_to_iff φ (n + 1) ((n + 1) + 1) rfl]
  simp only [liftCochain_fst, liftCochain_snd, Cochain.zero_comp, neg_eq_zero, true_and]
  tauto

theorem coneEnd_all_reconstruct
    (hzero : ∀ m (x : Cochain G F m), x = 0)
    (x : Cochain (mappingCone φ) (mappingCone φ) n) :
    coneEnd φ (coneEndA φ x) (coneEndB φ x) (coneEndC φ x) = x :=
  coneEnd_reconstruct φ x (hzero _ _)

theorem coneEnd_boundary_iff (m : ℤ) (hm : m + 1 = n)
    (a : Cochain G G m) (b : Cochain F F m) (c : Cochain F G (m - 1))
    (a' : Cochain G G n) (b' : Cochain F F n) (c' : Cochain F G m) :
    δ m n (coneEnd φ a b c) =
      descCochain φ (liftCochain φ b' c' hm)
        (liftCochain φ (0 : Cochain G F (n + 1)) a' rfl) hm ↔
      δ m n a = a' ∧ -(δ m n b) = b' ∧
        δ (m - 1) m c + b.comp (Cochain.ofHom φ) (add_zero m) +
          (m + 1).negOnePow • (Cochain.ofHom φ).comp a (zero_add m) = c' := by
  subst n
  rw [coneEnd_differential, ext_cochain_from_iff φ m (m + 1) rfl]
  simp only [inl_descCochain, inr_descCochain]
  rw [ext_cochain_to_iff φ m (m + 1) rfl,
    ext_cochain_to_iff φ (m + 1) ((m + 1) + 1) rfl]
  simp only [liftCochain_fst, liftCochain_snd, true_and]
  tauto

end ArExplicit

end

end OAI
