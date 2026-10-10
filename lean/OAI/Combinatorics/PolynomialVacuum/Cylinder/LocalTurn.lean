import OAI.Combinatorics.PolynomialVacuum.Cylinder.OrientationEquiv

namespace OAI

namespace PolynomialVacuumCylinder
open Classical
variable {M : ℕ}

 
def cubicTurn (a b c : ℤ) : ℤ := (a-b)*(b-c)*(c-a)/2
noncomputable def localTurn (r : Edge M →₀ ℤ) (v : Vertex M) : ℤ :=
  cubicTurn (orientedFlow r (v,0)) (orientedFlow r (v,1)) (orientedFlow r (v,2))

@[simp] theorem cubicTurn_zero : cubicTurn 0 0 0=0 := rfl
@[simp] theorem cubicTurn_neg (a b c : ℤ) : cubicTurn (-a) (-b) (-c)= -cubicTurn a b c := by
  unfold cubicTurn
  have he : (-a - -b)*(-b - -c)*(-c - -a)= -((a-b)*(b-c)*(c-a)) := by ring
  rw [he,Int.neg_ediv_of_dvd]
  have h : (a-b)*(b-c)*(c-a)%2=0 := by
    have ha : a%2=0 ∨ a%2=1 := by omega
    have hb : b%2=0 ∨ b%2=1 := by omega
    have hc : c%2=0 ∨ c%2=1 := by omega
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> rcases hc with hc | hc <;>
      simp [Int.mul_emod,Int.sub_emod,ha,hb,hc]
  exact Int.dvd_of_emod_eq_zero h

@[simp] theorem localTurn_neg (r : Edge M →₀ ℤ) (v : Vertex M) : localTurn (-r) v= -localTurn r v := by
  simp only [localTurn,map_neg,Finsupp.neg_apply,cubicTurn_neg]

theorem localTurn_contour (r : Edge M →₀ ℤ) (g : Germ M) (b : Bool)
    (h : LocalContour r g b) : localTurn r g.1=PolynomialVacuumBridge.Corridor.turnUnit b := by
  simp only [localTurn,h 0,h 1,h 2]
  rcases g with ⟨v,k⟩
  fin_cases k <;> cases b <;> simp [cubicTurn,outgoingSlot,Fin.ext_iff,PolynomialVacuumBridge.Corridor.turnUnit]

theorem contour_turns (r : Edge M →₀ ℤ) (g : Germ M) (w : List Bool)
    (h : WordContour r g w) :
    ((traced g w).map (localTurn r)).sum=PolynomialVacuumBridge.Corridor.turnUnits w := by
  induction w generalizing g with
  | nil => simp [traced,PolynomialVacuumBridge.Corridor.turnUnits]
  | cons b w ih =>
    simp only [traced,List.map_cons,List.sum_cons,localTurn_contour r g b h.1,ih _ h.2]
    rfl

theorem polygon_turn_sum (P : Polygon M) :
    (∑ v∈P.vertices,localTurn (polygonCurrent P) v)=PolynomialVacuumBridge.Corridor.turnUnits (polygonWord P) := by
  obtain ⟨hn,hN,hc,he⟩:=polygon_witness P
  have hv : P.vertices=(traced (polygonGerm P) (polygonWord P)).toFinset := by
    rw [Polygon.vertices,← he,closed_traced_edge_vertices _ _ hn hc]
  rw [hv]
  rw [List.sum_toFinset _ hN]
  exact contour_turns _ _ _ (simple_closed_word_contour _ _ hN hc)

end PolynomialVacuumCylinder

end OAI
