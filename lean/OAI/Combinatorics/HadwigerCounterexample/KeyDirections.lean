import OAI.Combinatorics.HadwigerCounterexample.CrossForms
import OAI.Combinatorics.HadwigerCounterexample.ImagePartitions

namespace OAI

/-! # Key Directions -/

noncomputable section
namespace HadwigerCounterexample
open scoped BigOperators
open Matrix Finset

variable {I : Type} [Fintype I]
variable {p : Shape} {n N : ℕ}

/-- One side of the lists, with actual point inputs, indexed by the
simultaneous (both units') list positions. Tags passed separately
because matched across the two sides. -/
structure Volley (p : Shape) (n : ℕ) (I : Type) where
  obj : I → Bool
  sel : I → Label p.b
  par : I → Base p.g n

abbrev Tagging (p : Shape) (I : Type) := I → Tag p.g
abbrev AtomKey {p : Shape} (l : Tag p.g) (N : ℕ) := TagStar l → Bool → Vec (Fin N)

def keyOne (p : Shape) (l : Tag p.g) (s : Label p.b) (z : Base p.g n)
    (o : Orient p n N) : AtomKey (p:=p) l N :=
  fun e b => primary (takeSign (p:=p) (o e.val) b) *ᵥ point p s z

abbrev Keys {p : Shape} {I : Type} (t : Tagging p I) (N : ℕ) := ∀ i, AtomKey (p:=p) (t i) N

namespace Volley
variable (v : Volley p n I)
def atomAt (t : Tagging p I) (i) := atom p (t i) (v.sel i) (v.par i)
def rayAt (i) := point p (v.sel i) (v.par i)
def rayLoc (i) := IP p n (v.obj i) *ᵥ v.rayAt i

/-- List from endpoint j to endpoint k of the other unit. -/
def shoots (w : I → Bool) (j k : Bool) := univ.filter (fun i => v.obj i=j ∧ w i=k)
def here (j : Bool) := Finset.univ.filter (fun i => v.obj i=j)
def sumAt (t : Tagging p I) (w : I→Bool) (j k : Bool) :=
  ∑ i∈shoots v w j k, v.atomAt t i

def keys (t : Tagging p I) (x : UnitType p n N) : Keys (p:=p) t N :=
  fun i => keyOne p (t i) (v.sel i) (v.par i) (onSide x (v.obj i))

abbrev visits (p : Shape) (t : Tagging p I) (e : Comp p.g) := {i:I//inc e (t i)}
instance (t : Tagging p I) (e) : Fintype (visits p t e) := inferInstance

def keyM (t : Tagging p I) (e : Comp p.g) : Mat (JointIdx p n) (visits p t e) :=
  Matrix.of fun i j => v.rayLoc j.val i
def keyPlan (t : Tagging p I) : Plan p n := fun e => colSp (v.keyM t e.1)

omit [Fintype I] in
theorem keys_loc (t : Tagging p I) (x : UnitType p n N) (i : I) (f : TagStar (t i)) (b : Bool) :
    v.keys t x i f b = images x (f.val,b) *ᵥ v.rayLoc i := by
  rw [rayLoc,mulVec_mulVec, images_ip]; rfl

omit [Fintype I] in
theorem atom_share (v' : Volley p n I) (t : Tagging p I) (x y : UnitType p n N)
    (h : v.keys t x=v'.keys t y) (i : I) :
    Uembed (onSide x (v.obj i)) (v.atomAt t i) = Uembed (onSide y (v'.obj i)) (v'.atomAt t i) := by
  classical
  funext e
  change liftM _ _ (atom p _ _ _ e) = liftM _ _ (atom p _ _ _ e)
  by_cases hs : inc e (t i)
  · simp only [atom_def,hs, ite_true,mom,liftM_outer]
    exact congrArg₂ vecMulVec (congr_fun (congr_fun (congr_fun h i) (⟨e,hs⟩)) true)
      (congr_fun (congr_fun (congr_fun h i) (⟨e,hs⟩)) false)
  simp only [atom_def,hs,ite_false,map_zero]

/-- At each endpoint at most q calls, with distinct labels and no
label interacting with a short vector in the pinned projections. -/
def avoids (a : Plan p n) (q : ℕ) :=
  ∀ i, ∃ B : Finset (Label p.b),
    (∀ z : Place p, protectedBy p (sPin a z i) q B) ∧
    (∀ j∈v.here i,v.sel j∉ B) ∧
    (v.here i).card ≤ q ∧
    Set.InjOn v.sel (v.here i : Set I)
end Volley

/-- Any combination of points with distinct labels has a short-ray representation
on the image label set. -/
theorem point_comb {p : Shape} {A : Type*} (J : Finset A) (s : A → Label p.b)
    (z : A → Base p.g n) (a : A → F) (hs : Set.InjOn s (J : Set A)) :
    ∃ u : LabVals p n, (∀ i∈J,u (s i)=a i • baseV (z i)) ∧
      ∑ i∈J,a i • point p (s i) (z i)=labcomb p n (J.image s) u := by
  classical
  let f := fun j : Label p.b => ∑ i∈J, if s i=j then a i • baseV (z i) else 0
  have he i (hi : i∈J) : f (s i)=a i • baseV (z i) := by
    unfold f
    rw [Finset.sum_eq_single i]
    · simp
    · intro j hj he; exact ite_eq_right (fun h => he (hs hj hi h))
    simp [hi]
  refine ⟨f,he,?_⟩
  rw [labcomb_eval,Finset.sum_image hs]
  exact Finset.sum_congr rfl fun i hi => by rw [he i hi,map_smul]; rfl

namespace Volley

variable (v : Volley p n I)

theorem key_miss (t : Tagging p I) {a : Plan p n} {q} (h : v.avoids a q)
    (e : Place p) (x : Vec (visits p t e.1))
    (hx : v.keyM t e.1 *ᵥ x ∈ tabSpace a e) : x=0 := by
  classical
  let M := v.keyM t e.1
  have he : M *ᵥ x = ∑ i : visits p t e.1,x i • (v.rayLoc i.val) := by
    rw [mulVec_eq_sum]
    simp_rw [op_smul_eq_smul]
    rfl
  funext j
  let i := v.obj j.val
  obtain ⟨B,hB,hj,hc,hsel⟩ := h i
  have hT := (tab_mem a e _).mp hx i
  let f (j : visits p t e.1) := v.obj j.val=i
  let J := univ.filter f
  have hg : ∑ j∈J,x j • v.rayAt j.val ∈ sPin a e i := by
    change ((IP p n i)ᵀ.mulVecLin (M *ᵥ x))∈_ at hT
    rw [he,map_sum] at hT
    have hi :
        (∑ j∈J,x j • v.rayAt j.val) =
        ∑ j : visits p t e.1,(IP p n i)ᵀ.mulVecLin (x j • v.rayLoc j.val) := by
      rw [show J = univ.filter f from rfl,Finset.sum_filter]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_smul,mulVecLin_apply,rayLoc,Matrix.mulVec_mulVec]
      by_cases hj : f j
      · rw [ite_eq_left hj,show v.obj j.val=i from hj,IP_self, Matrix.one_mulVec]
      rw [ite_eq_right hj,IP_cross (show i≠_ from Ne.symm hj), Matrix.zero_mulVec,smul_zero]
    rwa [hi]
  let s (x : visits p t e.1) := v.sel x.val
  have hh {j : visits p t e.1} (h : j∈J) : j.val∈v.here i :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,(mem_filter.mp h).2⟩
  have heq : Set.InjOn s (J : Set _) := fun j hj k hk h => Subtype.ext (hsel (hh hj) (hh hk) h)
  obtain ⟨u,hu,hZ⟩ := point_comb J s (v.par ∘ Subtype.val) x heq
  have hjj : j∈J := mem_filter.mpr ⟨mem_univ _,rfl⟩
  have hx : (J.image s).card ≤ q := by
    refine (card_image_le).trans (le_trans ?_ hc)
    have hsub : J.image Subtype.val ⊆ v.here i := by
      rintro x hx; obtain ⟨i,hi,rfl⟩ := mem_image.mp hx; exact hh hi
    rw [← card_image_of_injective J Subtype.val_injective]; exact card_le_card hsub
  have hz := hB e (J.image s) u (hZ ▸ hg) hx (s j) (mem_image_of_mem s hjj) (hj _ (hh hjj))
  rw [hu j hjj] at hz
  have heq := congr_fun hz none
  simpa only [Pi.zero_apply,Pi.smul_apply,smul_eq_mul,baseV,Option.elim',mul_one] using heq

theorem key_independent (t : Tagging p I) {a : Plan p n} {q} (h : v.avoids a q)
    (e : Place p) : Function.Injective (v.keyM t e.1).mulVec ∧
      Disjoint (v.keyPlan t e) (tabSpace a e) := by
  constructor
  · rw [← Matrix.coe_mulVecLin,← LinearMap.ker_eq_bot, Matrix.ker_mulVecLin_eq_bot_iff]
    intro x hx
    apply key_miss v t h e
    rw [hx]
    exact Submodule.zero_mem _
  rw [disjoint_iff_inf_le]
  rintro x ⟨⟨y,rfl⟩,hx⟩
  rw [key_miss v t h e y hx,map_zero]
  exact Submodule.zero_mem _
end Volley
end HadwigerCounterexample

end

end OAI
