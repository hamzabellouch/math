import OAI.MathematicalPhysics.ContinuumCoulomb.Quantum.QuantumRouteCongestion

namespace OAI

/-! Geometry only needs a bounded slot map injective inside each cell. This
interface permits the literal ordinal slot map without fixing abstract choices. -/

noncomputable section
namespace ContinuumCoulomb

structure QMACellSlots {Q : Type*} {rows width : ℕ}
    (cell : Q → QMAGridCell rows width) (A : ℕ) where
  index : Q → Fin A
  injective : ∀ {q r}, cell q = cell r → index q = index r → q=r

namespace QMACellSlots
variable {Q : Type*} {rows width A : ℕ} {cell : Q → QMAGridCell rows width}

 def ofDensity [Fintype Q]
    (h : ∀ p, (Finset.univ.filter (fun q => cell q=p)).card ≤ A) : QMACellSlots cell A :=
  ⟨qmaGridSlot cell h,qmaGridSlot_injective_on_cell cell h⟩

 def site (S : QMACellSlots cell A) (q : Q) : QMAFineGrid rows width A :=
  (finProdFinEquiv ((cell q).1,S.index q),(cell q).2)

 theorem site_injective (S : QMACellSlots cell A) : Function.Injective S.site := by
  intro q r h
  have hx := finProdFinEquiv.injective (congrArg Prod.fst h)
  have hrow : (cell q).1 = (cell r).1 :=
    congrArg (fun x : Fin (rows+1) × Fin A => x.1) hx
  have hcol : (cell q).2 = (cell r).2 :=
    congrArg (fun x : QMAFineGrid rows width A => x.2) h
  have hslot : S.index q = S.index r :=
    congrArg (fun x : Fin (rows+1) × Fin A => x.2) hx
  exact S.injective (Prod.ext hrow hcol) hslot

 theorem site_cell (S : QMACellSlots cell A) (hA : 0 < A) (q : Q) :
    qmaFineGridCell hA (S.site q) = cell q := by
  apply Prod.ext
  · apply Fin.ext
    change ((S.index q).val+A*(cell q).1.val)/A = (cell q).1.val
    rw [Nat.add_mul_div_left _ _ hA,Nat.div_eq_of_lt (S.index q).isLt,zero_add]
  · rfl

 theorem site_bounds (S : QMACellSlots cell A) (q : Q) (p : QMAGridCell rows width)
    (hne : QMAGridCellsNear (cell q) p) :
    (S.site q).1.val < (p.1.val+2)*A ∧ p.1.val*A ≤ (S.site q).1.val+A ∧
      (S.site q).2.val ≤ p.2.val+1 ∧ p.2.val ≤ (S.site q).2.val+1 := by
  obtain ⟨hr,hr',hc,hc'⟩ := hne
  have hs := (S.index q).isLt
  have hm := Nat.mul_le_mul_right A hr
  have hm' := Nat.mul_le_mul_right A hr'
  change (S.index q).val+A*(cell q).1.val < (p.1.val+2)*A ∧
    p.1.val*A ≤ (S.index q).val+A*(cell q).1.val+A ∧ _
  exact ⟨by nlinarith,by nlinarith,hc,hc'⟩

 theorem route_length (S : QMACellSlots cell A) (p q : Q)
    (a : QMAGridCell rows width) (hp : QMAGridCellsNear (cell p) a)
    (hq : QMAGridCellsNear (cell q) a) :
    qmaManhattanLength (qmaFineGridNat (S.site p)) (qmaFineGridNat (S.site q)) ≤ 3*A+2 := by
  obtain ⟨hp1,hp2,hp3,hp4⟩ := S.site_bounds p a hp
  obtain ⟨hq1,hq2,hq3,hq4⟩ := S.site_bounds q a hq
  simp only [Nat.add_mul] at hp1 hq1
  unfold qmaManhattanLength qmaFineGridNat Nat.dist
  omega

 def color (S : QMACellSlots cell A) (q : Q) : Fin 3 × Fin 3 × Fin A :=
  (⟨(cell q).1.val%3,Nat.mod_lt _ (by decide)⟩,
    ⟨(cell q).2.val%3,Nat.mod_lt _ (by decide)⟩,S.index q)

 theorem color_eq (S : QMACellSlots cell A) {p q : Q} (he : S.color p = S.color q)
    (hr : (cell p).1.val ≤ (cell q).1.val+2) (hr' : (cell q).1.val ≤ (cell p).1.val+2)
    (hc : (cell p).2.val ≤ (cell q).2.val+2) (hc' : (cell q).2.val ≤ (cell p).2.val+2) : p=q := by
  have hrow := congrArg (fun c : Fin 3 × Fin 3 × Fin A => c.1.val) he
  have hcol := congrArg (fun c : Fin 3 × Fin 3 × Fin A => c.2.1.val) he
  have hslot := congrArg (fun c : Fin 3 × Fin 3 × Fin A => c.2.2) he
  change (cell p).1.val%3 = (cell q).1.val%3 at hrow
  change (cell p).2.val%3 = (cell q).2.val%3 at hcol
  apply S.injective _ hslot
  apply Prod.ext <;> apply Fin.ext <;> omega

 theorem color_disjoint {E : Type*} (S : QMACellSlots cell A)
    (location : E → QMAGridCell rows width) (sites : Q → Finset E)
    (hl : ∀ q, ∀ z ∈ sites q, QMAGridCellsNear (location z) (cell q))
    {p q : Q} (hpq : p ≠ q) (he : S.color p = S.color q) : Disjoint (sites p) (sites q) := by
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  have hp := hl p z hz
  have hq := hl q z hz'
  apply hpq
  apply S.color_eq he <;> dsimp [QMAGridCellsNear] at hp hq <;> omega

end QMACellSlots
end ContinuumCoulomb

end

end OAI
