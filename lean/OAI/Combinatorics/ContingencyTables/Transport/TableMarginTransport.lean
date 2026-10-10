import OAI.Combinatorics.ContingencyTables.Transport.TableReindex

namespace OAI

/-! # Changing equal margin descriptions without changing entries -/

namespace ContingencyTables
variable {I J : Type*} [Fintype I] [Fintype J]

/-- Enumeration instances affect the proofs of the margins, never the entries. -/
def tableFintypeTransport (fi fi' : Fintype I) (fj fj' : Fintype J)
    (r : I → ℕ) (c : J → ℕ) : @Table I J fi fj r c ≃ @Table I J fi' fj' r c where
  toFun X := ⟨X.val,by
    cases Subsingleton.elim fi fi'
    cases Subsingleton.elim fj fj'
    exact X.property⟩
  invFun X := ⟨X.val,by
    cases Subsingleton.elim fi fi'
    cases Subsingleton.elim fj fj'
    exact X.property⟩
  left_inv X := rfl
  right_inv X := rfl

def tableMarginTransport (r r' : I → ℕ) (c c' : J → ℕ)
    (hr : r=r') (hc : c=c') : Table r c ≃ Table r' c' where
  toFun X := ⟨X.val,by rw [←hr,←hc]; exact X.property⟩
  invFun X := ⟨X.val,by rw [hr,hc]; exact X.property⟩
  left_inv X := rfl
  right_inv X := rfl

end ContingencyTables

end OAI
