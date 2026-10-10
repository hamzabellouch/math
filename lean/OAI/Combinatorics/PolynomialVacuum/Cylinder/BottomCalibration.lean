import OAI.Combinatorics.PolynomialVacuum.Cylinder.TurnMin
import OAI.Combinatorics.PolynomialVacuum.Cylinder.Indicator

namespace OAI

namespace PolynomialVacuumCylinder
open Classical
variable {M : ℕ}

def cylLayer : Vertex M → ℤ | .up _ j => j | .down _ j => j
@[simp] theorem cylLayer_project (v : PlaneVertex) : cylLayer (projectVertex M v)=layer v := by cases v <;> rfl

lemma closed_flow_below (g : Germ M) (w : List Bool) (j : ℤ)
    (hc : terminalGerm g w=g) (hH : ∀ v∈traced g w,j≤cylLayer v)
    (i : ZMod M) (k : ℤ) (hk : k<j) : wordFlow g w ((i,k),2)=0 := by
  have hn : Vertex.up i k∉traced g w := by
    intro h
    have hh := hH _ h
    change j≤k at hh
    omega
  have h := turnVisit_eq_zero_of_not_mem g w (.up i k) 2 hn
  rw [← orientedFlow_up,orientedFlow_wordFlow,hc,add_sub_cancel_right]
  exact h

lemma potential_below (g : Germ M) (w : List Bool) (j : ℤ)
    (hc : terminalGerm g w=g) (hH : ∀ v∈traced g w,j≤cylLayer v)
    (i : ZMod M) : potential (wordFlow g w) (i,j)=0 := by
  unfold potential
  rw [finitePrefix_eq_zero]
  · rfl
  · intro k hk
    by_contra hn
    have hz := closed_flow_below g w j hc hH (i+1) k (by omega)
    have hne : wordFlow g w ((i+1,k),2)≠0 := by
      simpa only [Finsupp.mem_support_iff,column_apply] using hk
    exact hne hz

lemma plane_potential_below (g : PlaneGerm) (w : List Bool) (j : ℤ)
    (hc : PolynomialVacuumBridge.Corridor.terminalGerm g w=g)
    (hH : ∀ v∈PolynomialVacuumBridge.Corridor.traced g w,j≤layer v)
    (p : PolynomialVacuumBridge.Corridor.FaceIndex →₀ ℤ)
    (hp : PolynomialVacuumBridge.Corridor.RepresentsFlow p (PolynomialVacuumBridge.Corridor.wordFlow g w))
    (i : ℤ) : p (i,j)=0 := by
  let m : ℤ := min (-(PolynomialVacuumBridge.Corridor.faceRadius p : ℤ)-1) j
  have hm : m≤j := min_le_right _ _
  have hmR : m≤ -(PolynomialVacuumBridge.Corridor.faceRadius p : ℤ)-1 := min_le_left _ _
  have hbase : p (i,m)=0 := by
    by_contra hn
    have h := (PolynomialVacuumBridge.Corridor.mem_support_in_box p (i,m) (Finsupp.mem_support_iff.mpr hn)).2
    dsimp only [Prod.snd] at h
    omega
  have hstep (k : ℤ) (hk : k<j) : p (i,k)=p (i,k+1) := by
    have hn : PolynomialVacuumBridge.Corridor.Vertex.up (i+1) k∉PolynomialVacuumBridge.Corridor.traced g w := by
      intro h
      have hh := hH _ h
      change j≤k at hh
      omega
    have ht := PolynomialVacuumBridge.Corridor.turnVisit_eq_zero_of_not_mem g w (.up (i+1) k) 2 hn
    have hf : PolynomialVacuumBridge.Corridor.orientedFlow (PolynomialVacuumBridge.Corridor.wordFlow g w) (.up (i+1) k,2)=0 := by
      rw [PolynomialVacuumBridge.Corridor.orientedFlow_wordFlow,hc,add_sub_cancel_right]
      exact ht
    rw [hp] at hf
    simp [PolynomialVacuumBridge.Corridor.leftFace,PolynomialVacuumBridge.Corridor.rightFace,
      PolynomialVacuumBridge.Corridor.reverseGerm,PolynomialVacuumBridge.Corridor.neighbor] at hf
    omega
  have hall : ∀ k, m≤k → k≤j → p (i,k)=0 := by
    intro k hk
    apply Int.leInduction (motive:=fun l _ => l≤j → p (i,l)=0) (fun _ => hbase) ?_ k hk
    intro l hl ih hlj
    have h := hstep l (by omega)
    rw [← h]
    exact ih (by omega)
  exact hall j hm le_rfl

 

lemma bottom_cylinder_sign (i j : ℤ) (b : Bool) (w : List Bool) (ε : ℤ)
    (hc : terminalGerm (projectGerm M (.up i j,if b then 2 else 1)) (b::w)=projectGerm M (.up i j,if b then 2 else 1))
    (hN : (traced (projectGerm M (.up i j,if b then 2 else 1)) (b::w)).Nodup)
    (hH : ∀ v∈PolynomialVacuumBridge.Corridor.traced (.up i j,if b then 2 else 1) (b::w), j≤layer v)
    (hvals : ∀ a, potential (wordFlow (projectGerm M (.up i j,if b then 2 else 1)) (b::w)) a=0 ∨
      potential (wordFlow (projectGerm M (.up i j,if b then 2 else 1)) (b::w)) a=ε) :
    ε=PolynomialVacuumBridge.Corridor.turnUnit b := by
  let g : Germ M := projectGerm M (.up i j,if b then 2 else 1)
  let p := potential (wordFlow g (b::w))
  have hb (z : ZMod M) : p (z,j)=0 := by
    apply potential_below g (b::w) j hc
    intro v hv
    rw [← project_traced] at hv
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hv
    simpa using hH u hu
  have hs := (localContour_sides p (wordFlow g (b::w)) (closed_word_has_potential g _ hc) g b
    (simple_closed_word_contour g _ hN hc).1).2.2
  cases b <;>
    simp [g,projectGerm,projectVertex,rightFace,leftFace,reverseGerm,neighbor] at hs
  · have hz := hb (i : ZMod M)
    have hv := hvals (((i : ZMod M)-1),j+1)
    change p _=0 ∨ p _=ε at hv
    change ε = (-1 : ℤ)
    omega
  · have hz := hb ((i : ZMod M)-1)
    have hv := hvals (((i : ZMod M)-1),j+1)
    change p _=0 ∨ p _=ε at hv
    change ε = (1 : ℤ)
    omega

lemma bottom_contractible_turn (i j : ℤ) (b : Bool) (w : List Bool)
    (hc : PolynomialVacuumBridge.Corridor.terminalGerm (.up i j,if b then 2 else 1) (b::w)=(.up i j,if b then 2 else 1))
    (hN : (PolynomialVacuumBridge.Corridor.traced (.up i j,if b then 2 else 1) (b::w)).Nodup)
    (hH : ∀ v∈PolynomialVacuumBridge.Corridor.traced (.up i j,if b then 2 else 1) (b::w), j≤layer v) :
    PolynomialVacuumBridge.Corridor.turnUnits (b::w)=6*PolynomialVacuumBridge.Corridor.turnUnit b := by
  let g : PlaneGerm := (.up i j,if b then 2 else 1)
  obtain ⟨p,ε,hp,hpn,hε,hvals⟩ := PolynomialVacuumBridge.Corridor.simple_closed_word_indicator g (b::w) (by simp) hN hc
  have hb (z : ℤ) : p (z,j)=0 := plane_potential_below g _ j hc hH p hp z
  have hs := (PolynomialVacuumBridge.Corridor.localContour_sides p (PolynomialVacuumBridge.Corridor.wordFlow g (b::w)) hp g b
    (PolynomialVacuumBridge.Corridor.simple_closed_word_contour g _ hN hc).1).2.2
  have ht := PolynomialVacuumBridge.Corridor.simple_polygon_signed_turn g (b::w) (by simp) hN hc p ε hp hpn hε hvals
  cases b <;>
    simp [g,PolynomialVacuumBridge.Corridor.rightFace,PolynomialVacuumBridge.Corridor.leftFace,
      PolynomialVacuumBridge.Corridor.reverseGerm,PolynomialVacuumBridge.Corridor.neighbor] at hs
  · have hz := hb i
    have hv := hvals (i-1,j+1)
    have he : ε = -1 := by omega
    rw [he] at ht
    change PolynomialVacuumBridge.Corridor.turnUnits (false::w)=6*(-1 : ℤ)
    omega
  · have hz := hb (i-1)
    have hv := hvals (i-1,j+1)
    have he : ε=1 := by omega
    rw [he] at ht
    change PolynomialVacuumBridge.Corridor.turnUnits (true::w)=6*(1 : ℤ)
    omega

end PolynomialVacuumCylinder

end OAI
