import OAI.Analysis.LipschitzHilbert.Geometry.SourceTwoSidedSizeSelection

namespace OAI

/-! A literal one-packet separated test controls each coefficient.
The top direction is chosen inside its actual half-open angular cell. -/
noncomputable section
open Set
open scoped BigOperators
namespace LipschitzHilbert

private theorem interval_far_point (a d theta : ℝ) (hd : 0<d) :
    ∃ s∈Ico a (a+d), d/4≤|s-theta| := by
  by_cases h : d/4≤|a-theta|
  · exact ⟨a,⟨le_rfl,by linarith⟩,h⟩
  · have hh := abs_lt.mp (lt_of_not_ge h)
    refine ⟨a+d/2,⟨by linarith,by linarith⟩,?_⟩
    exact (by linarith [hh.1] : d/4≤a+d/2-theta).trans (le_abs_self _)

namespace SourceLabeledLattice
variable {N : ℕ} {κ : Type} {Label : Fin N → Type} {Item : ∀ j, Label j → Type}
  [Fintype κ] [∀ j l, Fintype (Item j l)]
variable (P : SourceLabeledLattice N κ Label Item)
attribute [local instance] Classical.propDecidable Classical.decEq

theorem exists_one_packet_size_direction (w cb : ℝ) (hw : 0<w) (hcb : cb≤1/4)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ) (q : P.PacketIndex) :
    ∃ t∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1),
      cb*w/P.length q.1≤|t-P.rowSlope q.1 q.2.1| := by
  let u := w/P.topLength
  let k : ℤ := q.1.val
  let j := cell q.1 q.2.1
  let a := u*DyadicLineGrid.left grid k j
  let d := u*DyadicLineGrid.scale k
  have hu : 0<u := div_pos hw P.topLength_pos
  have hd : 0<d := mul_pos hu (DyadicLineGrid.scale_pos k)
  have hnext : DyadicLineGrid.left grid k (j+1)=
      DyadicLineGrid.left grid k j+DyadicLineGrid.scale k := by
    unfold DyadicLineGrid.left
    push_cast
    ring
  have hcell : Ico a (a+d)⊆scaledAngularCell u grid k j := by
    intro t ht
    change DyadicLineGrid.left grid k j≤t/u ∧ t/u<DyadicLineGrid.left grid k (j+1)
    constructor
    · apply (le_div_iff₀ hu).mpr
      simpa only [a,mul_comm] using ht.1
    · apply (div_lt_iff₀ hu).mpr
      rw [hnext]
      simpa only [a,d,add_mul,mul_add,mul_comm] using ht.2
  have hdEq : d=w/P.length q.1 := by
    dsimp only [d,u,k,length,DyadicLineGrid.scale]
    rw [zpow_natCast]
    field_simp [P.topLength_pos.ne']
  obtain ⟨t,ht,hfar⟩ := interval_far_point a d (P.rowSlope q.1 q.2.1) hd
  refine ⟨t,hcell ht,?_⟩
  calc
    cb*w/P.length q.1 = cb*d := by rw [hdEq,mul_div_assoc]
    _ ≤ d/4 := by nlinarith
    _ ≤ _ := hfar

theorem coefficient_le_of_size_tests
    (w cb tau sigma : ℝ) (hw : 0<w) (hcb : cb≤1/4) (hsigma : 0≤sigma)
    (cell : ∀ j, P.labels j → ℤ) (grid : ℤ)
    (c : ∀ j (l : P.labels j), Item j l → EuclideanSpace ℂ κ)
    (R : Finset P.PacketIndex)
    (hsize : ∀ T : SlopeBox, T.width=P.width → T.length≤tau →
      P.unsignedSizeTestEnergy w cb cell grid c R T≤sigma^2*T.area)
    (q : P.PacketIndex) (hq : q∈R) (hlen : P.length q.1≤tau) :
    ‖c q.1 q.2.1 q.2.2‖≤sigma := by
  obtain ⟨t,ht,hsep⟩ := P.exists_one_packet_size_direction w cb hw hcb cell grid q
  let T : SlopeBox := ⟨P.actualX q.1 q.2.1 q.2.2,P.actualZ q.1 q.2.1 q.2.2,t,
    P.length q.1,P.width,P.length_pos q.1,P.width_pos⟩
  have hsp : (P.actualX q.1 q.2.1 q.2.2,P.actualZ q.1 q.2.1 q.2.2)∈densitySpatialBox T (1/2) := by
    change |P.actualX q.1 q.2.1 q.2.2-P.actualX q.1 q.2.1 q.2.2|≤1/2*P.length q.1 ∧
      |(P.actualZ q.1 q.2.1 q.2.2-P.actualZ q.1 q.2.1 q.2.2)-
        t*(P.actualX q.1 q.2.1 q.2.2-P.actualX q.1 q.2.1 q.2.2)|≤1/2*P.width
    simp only [sub_self,mul_zero,abs_zero]
    exact ⟨mul_nonneg (by norm_num) (P.length_pos q.1).le,
      mul_nonneg (by norm_num) P.width_pos.le⟩
  have hguard : P.length q.1≤T.length ∧
      (P.actualX q.1 q.2.1 q.2.2,P.actualZ q.1 q.2.1 q.2.2)∈densitySpatialBox T (1/2) ∧
      T.slope∈scaledAngularCell (w/P.topLength) grid q.1.val (cell q.1 q.2.1) ∧
      cb*w/P.length q.1≤|T.slope-P.rowSlope q.1 q.2.1| := ⟨le_rfl,hsp,ht,hsep⟩
  have henergy : ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width≤
      P.unsignedSizeTestEnergy w cb cell grid c R T := by
    have h := Finset.single_le_sum (s:=R) (f:=fun p : P.PacketIndex =>
      if P.length p.1≤T.length ∧
        (P.actualX p.1 p.2.1 p.2.2,P.actualZ p.1 p.2.1 p.2.2)∈densitySpatialBox T (1/2) ∧
        T.slope∈scaledAngularCell (w/P.topLength) grid p.1.val (cell p.1 p.2.1) ∧
        cb*w/P.length p.1≤|T.slope-P.rowSlope p.1 p.2.1| then
        ‖c p.1 p.2.1 p.2.2‖^2*P.length p.1*P.width else 0)
      (fun p _ => by
        split_ifs
        · exact mul_nonneg (mul_nonneg (sq_nonneg _) (P.length_pos p.1).le) P.width_pos.le
        · exact le_rfl) hq
    dsimp only [unsignedSizeTestEnergy]
    simpa only [ite_eq_left hguard] using h
  have he := henergy.trans (hsize T rfl hlen)
  change ‖c q.1 q.2.1 q.2.2‖^2*P.length q.1*P.width≤sigma^2*(P.length q.1*P.width) at he
  have hsq : ‖c q.1 q.2.1 q.2.2‖^2≤sigma^2 := by
    apply (mul_le_mul_iff_left₀ (mul_pos (P.length_pos q.1) P.width_pos)).mp
    simpa only [mul_assoc,mul_comm,mul_left_comm] using he
  nlinarith [norm_nonneg (c q.1 q.2.1 q.2.2)]

end SourceLabeledLattice
end LipschitzHilbert

end

end OAI
