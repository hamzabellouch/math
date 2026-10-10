import OAI.Geometry.HeilbronnTriangle.NormDeterminant
import OAI.Geometry.HeilbronnTriangle.Definitions

namespace OAI


noncomputable section

namespace Problem355.FiniteFieldLabels

variable (p : ℕ) [Fact p.Prime]

abbrev Label := GaloisField p heilbronnD

def labelBasis : Module.Basis (Fin heilbronnD) (ZMod p) (Label p) :=
  (Module.finBasis (ZMod p) (Label p)).reindex
    (finCongr (GaloisField.finrank p (by norm_num [heilbronnD])))

theorem card_label : Nat.card (Label p) = p ^ heilbronnD :=
  GaloisField.card p heilbronnD (by norm_num [heilbronnD])

theorem finrank_label : Module.finrank (ZMod p) (Label p) = heilbronnD :=
  GaloisField.finrank p (by norm_num [heilbronnD])

def labelNormPolynomial :
    MvPolynomial (NormDeterminant.Variables (Fin heilbronnD)) (ZMod p) :=
  NormDeterminant.normDeterminantPolynomial (F := ZMod p) (labelBasis p)

def labelVector (x : Label p) : Fin 3 × Fin heilbronnD → ZMod p :=
  NormDeterminant.labelCoordinates (labelBasis p) x

theorem swap_labelNormPolynomial {a b : Fin 3} (hab : a ≠ b) :
    MvPolynomial.rename (NormDeterminant.groupRename (Equiv.swap a b))
      (labelNormPolynomial p) = -labelNormPolynomial p := by
  apply NormDeterminant.swap_normDeterminantPolynomial _ _ hab
  rw [finrank_label]
  norm_num [heilbronnD]

theorem eval_labelNormPolynomial_ne_zero {x y z : Label p}
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    MvPolynomial.eval (fun v => labelVector p (![x, y, z] v.1) v.2)
      (labelNormPolynomial p) ≠ 0 :=
  NormDeterminant.eval_normDeterminantPolynomial_labels_ne_zero (labelBasis p)
    hxy hxz hyz

end Problem355.FiniteFieldLabels

end

end OAI
