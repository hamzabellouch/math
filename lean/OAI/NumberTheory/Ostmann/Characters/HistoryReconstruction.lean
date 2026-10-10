import OAI.NumberTheory.Ostmann.Characters.HistoryUniquenessRange

namespace OAI

namespace Ostmann.Characters.HistoryReconstruction

structure Plan where
  copiedSize : ℕ → ℕ
  previousOrder : ℕ → List ℕ

def leftProduct (m:ℕ) (x:List ℤ) : ℤ := (x.take m).prod

def rightProduct (m:ℕ) (x:List ℤ) : ℤ := ((x.drop m).take m).prod

def pivot (m:ℕ) (x:List ℤ) (s v w:ℤ) : ℤ :=
  (v*rightProduct m x-w*leftProduct m x)/s

def childState (plan:Plan) (k:ℕ) (right:Bool) (x:List ℤ) (P:ℤ) : List ℤ :=
  let m := plan.copiedSize k
  let h := if right then (x.drop m).take m else x.take m
  let y := x.drop (2*m)
  let old := P::(h++y)
  (plan.previousOrder k).map (fun i=>old[i]?.getD 0)

@[reducible] def Tree : ℕ → Type
  | 0 => PUnit
  | k+1 => (ℤ×ℤ) × (Tree k × Tree k)

structure NodeValid (m:ℕ) (x:List ℤ) (s v w B V:ℤ) : Prop where
  root_ne_zero : s≠0
  right_pos : 0<rightProduct m x
  pivot_pos : 0<pivot m x s v w
  pivot_le : pivot m x s v w≤B
  left_frequency_le : |v|≤V
  right_frequency_le : |w|≤V
  range_gap : 2*B*V<rightProduct m x
  integral : s∣v*rightProduct m x-w*leftProduct m x
  root_unit : IsCoprime s (rightProduct m x)
  pivot_unit : IsCoprime (pivot m x s v w) w

theorem NodeValid.unique {m:ℕ} {x:List ℤ} {s v w v' w' B V:ℤ}
    (h:NodeValid m x s v w B V) (h':NodeValid m x s v' w' B V) : v=v' ∧ w=w' := by
  have he : v*rightProduct m x-w*leftProduct m x=s*pivot m x s v w := by
    exact (Int.mul_ediv_cancel' h.integral).symm
  have he' : v'*rightProduct m x-w'*leftProduct m x=s*pivot m x s v' w' := by
    exact (Int.mul_ediv_cancel' h'.integral).symm
  exact (reversal_unique_of_range he he' h.root_ne_zero h.right_pos
    h.pivot_pos h'.pivot_pos h.pivot_le h'.pivot_le h.right_frequency_le h'.right_frequency_le
    h.range_gap h.root_unit h.pivot_unit h'.pivot_unit).imp_right (fun hh=>hh.1)

@[reducible] def Valid (plan:Plan) (B V:ℕ→List ℤ→ℤ) :
    (k:ℕ) → ℤ → List ℤ → Tree k → Prop
  | 0,_,_,_ => True
  | k+1,s,x,t =>
      NodeValid (plan.copiedSize k) x s t.1.1 t.1.2 (B k x) (V k x) ∧
      Valid plan B V k t.1.1
        (childState plan k false x (pivot (plan.copiedSize k) x s t.1.1 t.1.2)) t.2.1 ∧
      Valid plan B V k t.1.2
        (childState plan k true x (pivot (plan.copiedSize k) x s t.1.1 t.1.2)) t.2.2

theorem valid_unique (plan:Plan) (B V:ℕ→List ℤ→ℤ) (k:ℕ)
    (s:ℤ) (x:List ℤ) (t t':Tree k)
    (h:Valid plan B V k s x t) (h':Valid plan B V k s x t') : t=t' := by
  induction k generalizing s x with
  | zero => exact Subsingleton.elim _ _
  | succ k ih =>
    rcases t with ⟨⟨v,w⟩,l,r⟩
    rcases t' with ⟨⟨v',w'⟩,l',r'⟩
    obtain ⟨hv,hw⟩ := NodeValid.unique h.1 h'.1
    change v=v' at hv
    change w=w' at hw
    subst v'
    subst w'
    have hl := ih _ _ l l' h.2.1 h'.2.1
    have hr := ih _ _ r r' h.2.2 h'.2.2
    subst l'
    subst r'
    rfl

theorem valid_subsingleton (plan:Plan) (B V:ℕ→List ℤ→ℤ) (k:ℕ) (s:ℤ) (x:List ℤ) :
    Set.Subsingleton {t:Tree k | Valid plan B V k s x t} := by
  intro t ht t' ht'
  exact valid_unique plan B V k s x t t' ht ht'

end Ostmann.Characters.HistoryReconstruction

end OAI
