import OAI.Combinatorics.PolynomialVacuum.Cylinder.DomainWeight
import OAI.Combinatorics.PolynomialVacuum.Cylinder.BoundaryCanonical

namespace OAI

namespace PolynomialVacuumCylinder
open Classical PolynomialVacuumAlgebra
variable {M : ℕ}

theorem columnTotal_add (q r : Edge M →₀ ℤ) (i : ZMod M) :
    columnTotal (q+r) i=columnTotal q i+columnTotal r i := by
  have he : column (q+r) i 2=column q i 2+column r i 2 := by ext; rfl
  unfold columnTotal
  rw [he,Finsupp.sum_add_index] <;> simp

private theorem local_weight_zero (q : Edge M →₀ ℤ) (v : Vertex M)
    (hz : ∀k,orientedFlow q (v,k)=0) : localCurrentWeight q v=1 := by
  rw [local_weight_shape q v (Or.inl hz)]
  have hn : v∉activeSites q := by simp only [mem_activeSites]; push Not; exact hz
  simp [hn,localTurn,hz]

theorem local_weight_add (q r : Edge M →₀ ℤ) (v : Vertex M)
    (hd : v∉activeSites q ∨ v∉activeSites r) :
    localCurrentWeight (q+r) v=localCurrentWeight q v*localCurrentWeight r v := by
  rcases hd with hq | hr
  · have hz : ∀k,orientedFlow q (v,k)=0 := by simpa only [mem_activeSites,not_exists,not_not] using hq
    rw [local_weight_zero q v hz,one_mul]
    simp only [localCurrentWeight,map_add,Finsupp.add_apply,hz,zero_add]
  · have hz : ∀k,orientedFlow r (v,k)=0 := by simpa only [mem_activeSites,not_exists,not_not] using hr
    rw [local_weight_zero r v hz,mul_one]
    simp only [localCurrentWeight,map_add,Finsupp.add_apply,hz,add_zero]

 

theorem domainWeight_add (D : Finset (Vertex M)) (q r : Edge M →₀ ℤ)
    (hd : Disjoint (D∩activeSites q) (D∩activeSites r)) :
    domainWeight D (q+r)=domainWeight D q*domainWeight D r := by
  have hz : zeta≠0 := by simp
  have hl (v : Vertex M) (hv : v∈D) : localCurrentWeight (q+r) v=
      localCurrentWeight q v*localCurrentWeight r v := by
    apply local_weight_add
    by_cases hq : v∈activeSites q
    · right
      intro hr
      exact Finset.disjoint_left.mp hd (Finset.mem_inter.mpr ⟨hv,hq⟩) (Finset.mem_inter.mpr ⟨hv,hr⟩)
    · exact Or.inl hq
  simp only [domainWeight,columnTotal_add,zpow_add₀ hz]
  rw [Finset.prod_congr rfl hl,Finset.prod_mul_distrib]
  ring

@[simp] theorem traced_length (g : Germ M) (w : List Bool) : (traced g w).length=w.length := by
  induction w generalizing g with
  | nil => rfl
  | cons b w ih => simp [traced,ih]

theorem contour_active (q : Edge M →₀ ℤ) (g : Germ M) (w : List Bool)
    (hc : WordContour q g w) : ∀v∈traced g w,v∈activeSites q := by
  induction w generalizing g with
  | nil => simp [traced]
  | cons b w ih =>
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · apply (mem_activeSites q g.1).mpr
      refine ⟨g.2,?_⟩
      have hh:=hc.1 g.2
      simp only [Ne.symm (outgoingSlot_ne g b),ite_false,ite_true,zero_sub] at hh
      rw [hh]
      norm_num
    · exact ih _ hc.2 v hv

namespace BoundaryArc
variable {D : Finset (Vertex M)} (A : BoundaryArc D)

theorem domain_active : D∩activeSites A.current=A.vertices := by
  ext v
  rw [Finset.mem_inter]
  constructor
  · rintro ⟨hv,hq⟩
    by_contra hn
    obtain ⟨k,hk⟩:=(mem_activeSites A.current v).mp hq
    exact hk (A.current_zero v hv hn k)
  · intro hv
    exact ⟨A.vertices_subset hv,contour_active _ _ _ A.contour v (List.mem_toFinset.mp hv)⟩

theorem domain_turn : domainTurn D A.current=PolynomialVacuumBridge.Corridor.turnUnits A.word := by
  have hs : (∑v∈D,localTurn A.current v)=∑v∈A.vertices,localTurn A.current v := by
    symm
    apply Finset.sum_subset A.vertices_subset
    intro v hv hn
    simp [localTurn,A.current_zero v hv hn]
  rw [domainTurn,hs]
  unfold vertices
  rw [List.sum_toFinset _ A.distinct]
  exact contour_turns _ _ _ A.contour

noncomputable def weight : ℂ :=
  xStar^A.word.length * loopTurnPhase (PolynomialVacuumBridge.Corridor.turnUnits A.word) * zeta^(columnTotal A.current 1)

theorem domain_weight : domainWeight D A.current=A.weight := by
  have hn : domainOccupation D A.current=A.word.length := by
    rw [domainOccupation,A.domain_active]
    change (traced A.start A.word).toFinset.card=A.word.length
    rw [List.toFinset_card_of_nodup A.distinct]
    exact traced_length _ _
  rw [domainWeight,local_product_shape D A.current A.local_ice,hn,A.domain_turn]
  rfl
end BoundaryArc
end PolynomialVacuumCylinder

end OAI
