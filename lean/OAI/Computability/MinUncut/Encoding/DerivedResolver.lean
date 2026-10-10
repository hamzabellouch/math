import Mathlib
import OAI.Computability.MinUncut.Analysis.GaussianQuadrature

namespace OAI

namespace MinUncut.Preprocess
open MinUncut.FiniteGaussian

private theorem encode_ofLeftInjection_canonical {α β : Type*} (e : α ≃ ℕ)
    (f : β → α) (g : α → Option β) (hfg : ∀ b, g (f b) = some b)
    (hgf : ∀ a b, g a = some b → f b = a) (n : ℕ) (b : β)
    (h : @Encodable.decode β
      (@Encodable.ofLeftInjection α β (Encodable.ofEquiv ℕ e) f g hfg) n = some b) :
    @Encodable.encode β
      (@Encodable.ofLeftInjection α β (Encodable.ofEquiv ℕ e) f g hfg) b = n := by
  change (some (e.symm n)).bind g = some b at h
  change e (f b) = n
  rw [hgf _ _ (by simpa using h), e.apply_symm_apply]

abbrev oldGridEncode (g : GridData) : ℕ := @Encodable.encode GridData instEncodableGridData g
abbrev oldGridDecode (n : ℕ) : Option GridData := @Encodable.decode GridData instEncodableGridData n

lemma oldGridEncode_eq (g : GridData) : oldGridEncode g=Nat.pair (Nat.pair 0 0+1)
  (Nat.pair (Nat.pair 0 g.T+1) (Nat.pair (Nat.pair 0 g.L+1) (Nat.pair (Nat.pair 0 g.r+1) (Nat.pair 0 0)))) := rfl

lemma oldGridDecode_canonical (n : ℕ) (g : GridData) (h : oldGridDecode n=some g) :
    oldGridEncode g=n := by
  apply encode_ofLeftInjection_canonical (h := h)
  intro tree result htree
  cases tree with
  | nat _ => cases htree
  | cons tag fields =>
    cases tag with
    | cons _ _ => cases htree
    | nat tag =>
      cases tag with
      | succ _ => cases htree
      | zero =>
        cases fields with
        | nat _ => cases htree
        | cons t fields =>
          cases t with
          | cons _ _ => cases htree
          | nat t =>
            cases fields with
            | nat _ => cases htree
            | cons l fields =>
              cases l with
              | cons _ _ => cases htree
              | nat l =>
                cases fields with
                | nat _ => cases htree
                | cons r fields =>
                  cases r with
                  | cons _ _ => cases htree
                  | nat r =>
                    cases fields with
                    | cons _ _ => cases htree
                    | nat last =>
                      cases last with
                      | succ _ => cases htree
                      | zero =>
                        cases htree
                        rfl

end MinUncut.Preprocess

end OAI
