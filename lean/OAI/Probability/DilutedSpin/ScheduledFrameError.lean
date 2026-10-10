import OAI.Probability.DilutedSpin.HeightTransport
import OAI.Probability.DilutedSpin.PrefixProjection

namespace OAI

section
section
namespace DilutedSpinGlass.ReducedTopology
open scoped BigOperators
variable {Ω α I : Type} [Fintype Ω] [Fintype α] [DecidableEq α]
  [Fintype I] [DecidableEq I] {N : ℕ}

 
theorem shiftedFrameHeight (H r d : ℕ) : H+1+(r+1)+1+d=H+1+1+r+1+d := by omega

/-- The literal two delayed target sides, retaining all old depth coordinates. -/
def delayedFrame (H r d : ℕ) (k : ℕ+) (C : Fin k → ReducedTopology)
    (q : (j : Fin k) → (C j).Vertex → ℕ) : PrescribedTree (H+1+1+r+1+d) :=
  PrescribedTree.heightCast (shiftedFrameHeight H r d)
    (PrescribedTree.splitFrame (.node k (fun j => realize H (r+1+1+d+1) (C j) (fun v => q j v+1)))
      (r+1) d)

/-- Complete target projection comparison at the SAME height as the old
frame. Both projectors and both entire target sides are the literal
scheduled trees. No desired covariance estimate is an input. -/
theorem scheduled_frame_target_error_le (H r d : ℕ) (k : ℕ+) (hk : 2≤(k:ℕ))
    (a : α) (C : Fin k → ReducedTopology)
    (e : (j : Fin k) → (C j).Vertex → {j : α // j≠a})
    (Q : α → Fin (H+1+1+r+1+d)) (ha : (Q a).val=r+1+d)
    (hQ : ∀ j v, (Q a).val+1≤(Q (e j v)).val)
    (T : KernelTower Ω (H+1+1+r+1+d))
    (f : FinitePath Ω (H+1+1+r+1+d) → Fin N → ℝ) (hf : ∀ x i, |f x i|≤1) :
    let ht := shiftedFrameHeight H r d
    let OldChild := fun j => realize (H+1) (r+1+d+1) (C j) (fun v => (Q (e j v)).val)
    let NewChild := fun j => realize H (r+1+1+d+1) (C j) (fun v => (Q (e j v)).val+1)
    let RawTarget := PrescribedTree.splitFrame (.node k NewChild) (r+1) d
    let Target := PrescribedTree.heightCast ht RawTarget
    let T' := kernelHeightCast ht.symm T
    let f' := vectorHeightCast ht.symm f
    ∀ (b : (PrescribedTree.node k NewChild).Leaf) (q0 : I → RawTarget.Leaf),
      Function.Bijective q0 → ∀ (u v : I),
      q0 u=PrescribedTree.splitFrameLeaf (.node k NewChild) (r+1) d 0 b →
      q0 v=PrescribedTree.splitFrameLeaf (.node k NewChild) (r+1) d 1 b →
    let q := fun j => PrescribedTree.leafHeightCast ht RawTarget (q0 j)
    PrescribedTree.matrixProjectionError Target q T u v
      (PrescribedTree.spatialProduct (fun _ : I => f))
      (fun x i => PrescribedTree.splitProjector (.node k OldChild) r d T (fun y => f y i) x) ≤
      2*Real.sqrt ((k:ℝ)*∑ j, Real.sqrt (PrescribedTree.descendantEnergyAt (NewChild j) (r+1) d T' f'))+
        projectionShiftError a C e T f Q := by
  dsimp only
  intro b q0 hq u v hu hv
  let ht := shiftedFrameHeight H r d
  let L := H+1+1+r+1+d
  let L' := H+1+(r+1)+1+d
  let Q' : α → Fin L' := fun j => Fin.cast ht.symm (Q j)
  let T' := kernelHeightCast ht.symm T
  let f' := vectorHeightCast ht.symm f
  let NewChild := fun j => realize H (r+1+1+d+1) (C j) (fun v => (Q (e j v)).val+1)
  let RawTarget := PrescribedTree.splitFrame (.node k NewChild) (r+1) d
  have hf' : ∀ x i, |f' x i|≤1 := fun x i => hf (pathHeightCast ht x) i
  have hnew := delayed_target_projection_le (I := I) H (r+1) d k hk a C e Q'
    (by simpa only [Q',Fin.val_cast] using ha)
    (fun j v => by simpa only [Q',Fin.val_cast] using hQ j v) T' f' hf'
  dsimp only at hnew
  simp only [Q',Fin.val_cast] at hnew
  have he := hnew b q0 hq u v hu hv
  have hp := scheduled_splitProjector_product (H+1) r d k hk C
    (fun j w => (Q (e j w)).val)
    (fun j w => by have := hQ j w; omega) T f
  simp only [realize,rootSchedule,lt_self_iff_false,ite_false] at hp
  rw [hp]
  have hcast := PrescribedTree.matrixProjectionError_heightCast ht RawTarget q0 T' u v f'
    (conditionalScheduledProduct L' 0 (Q a).val C (fun j w => (Q (e j w)).val) T' f')
  rw [conditionalScheduledProduct_heightCast] at hcast
  dsimp only [T',f'] at hcast
  simp only [kernelHeightCast_inv,vectorHeightCast_inv] at hcast
  simp only [ha] at hcast he
  rw [hcast]
  have hh := projectionShiftError_heightCast ht.symm a C e T f Q
  change projectionShiftError a C e T' f' Q'=projectionShiftError a C e T f Q at hh
  change _ ≤ _+projectionShiftError a C e T' f' (fun j => Q' j) at he
  rw [hh] at he
  exact he

end DilutedSpinGlass.ReducedTopology
end

end

section
section
namespace DilutedSpinGlass
variable {Ω : Type} [Fintype Ω] {n m N : ℕ}

@[simp] lemma kernelHeightCast_succ_fst (h : n+1=m+1) (T : KernelTower Ω (n+1)) :
    (kernelHeightCast h T).1=T.1 := by
  have hm := Nat.succ.inj h
  subst m
  rfl

@[simp] lemma kernelHeightCast_succ_snd (h : n+1=m+1) (T : KernelTower Ω (n+1)) (x : Ω) :
    (kernelHeightCast h T).2 x=kernelHeightCast (Nat.succ.inj h) (T.2 x) := by
  have hm := Nat.succ.inj h
  subst m
  rfl

omit [Fintype Ω] in
@[simp] lemma vectorHeightCast_succ_pair (h : n+1=m+1)
    (f : FinitePath Ω (n+1) → Fin N → ℝ) (x : Ω) (y : FinitePath Ω m) :
    vectorHeightCast h f (x,y)=vectorHeightCast (Nat.succ.inj h) (fun z => f (x,z)) y := by
  have hm := Nat.succ.inj h
  subst m
  rfl

namespace PrescribedTree
/-- A proper-child covariance is the SAME single-copy covariance evaluated at
the child's retained evaluation coordinate. Its two successive prefix averages
are just one original-kernel prefix, not an independent pair of copies. -/
lemma descendantEnergyAt_eq_shapeEnergyAt (C : PrescribedTree n) (r d : ℕ)
    (T : KernelTower Ω (n+1+r+1+d)) (f : FinitePath Ω (n+1+r+1+d) → Fin N → ℝ) :
    descendantEnergyAt C r d T f = shapeEnergyAt C (r+1+d)
      (kernelHeightCast (by omega) T) (vectorHeightCast (by omega) f) := by
  induction d with
  | zero => rfl
  | succ d ih =>
    simp only [descendantEnergyAt,shapeEnergyAt,kernelHeightCast_succ_fst,
      kernelHeightCast_succ_snd,vectorHeightCast_succ_pair]
    apply FiniteLaw.expect_congr
    intro x
    exact ih (T.2 x) (fun y => f (x,y))

end PrescribedTree
end DilutedSpinGlass
end

end

end OAI
