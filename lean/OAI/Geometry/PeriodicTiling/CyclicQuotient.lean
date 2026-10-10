import OAI.Geometry.PeriodicTiling.TilingBasic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum

namespace OAI

namespace PeriodicTilingThree
namespace CyclicQuotient

abbrev Group (Q : ℕ) := Plane × ZMod Q

def projection (Q : ℕ) : Lattice 3 →+ Group Q where
  toFun z := ((z 0, z 1), (z 2 : ZMod Q))
  map_zero' := by simp
  map_add' x y := by simp

def kernelStep (Q : ℕ) : Lattice 3 := ![0, 0, (Q : ℤ)]

@[simp] theorem projection_kernelStep (Q : ℕ) :
    projection Q (kernelStep Q) = 0 := by
  simp [projection, kernelStep]

theorem kernelStep_ne_zero (Q : ℕ) [NeZero Q] : kernelStep Q ≠ 0 := by
  intro h
  have hz : (Q : ℤ) = 0 := by
    simpa [kernelStep] using congrFun h 2
  exact (NeZero.ne Q) (Int.ofNat_inj.mp hz)

def lift (Q : ℕ) (g : Group Q) : Lattice 3 :=
  ![g.1.1, g.1.2, (g.2.val : ℤ)]

@[simp] theorem projection_lift (Q : ℕ) [NeZero Q] (g : Group Q) :
    projection Q (lift Q g) = g := by
  rcases g with ⟨⟨x, y⟩, r⟩
  simp [projection, lift]

@[simp] theorem lift_zero (Q : ℕ) : lift Q 0 = 0 := by
  ext i
  fin_cases i <;> simp [lift]

theorem projection_surjective (Q : ℕ) [NeZero Q] :
    Function.Surjective (projection Q) :=
  fun g => ⟨lift Q g, projection_lift Q g⟩

theorem lift_injective (Q : ℕ) [NeZero Q] : Function.Injective (lift Q) := by
  intro g h hgh
  have he := congrArg (projection Q) hgh
  simpa only [projection_lift] using he

theorem mem_ker_iff_zsmul_kernelStep (Q : ℕ) (z : Lattice 3) :
    z ∈ (projection Q).ker ↔ ∃ k : ℤ, z = k • kernelStep Q := by
  constructor
  · intro hz
    have hp : projection Q z = 0 := hz
    have h0 : z 0 = 0 := congrArg (fun g : Group Q => g.1.1) hp
    have h1 : z 1 = 0 := congrArg (fun g : Group Q => g.1.2) hp
    have h2 : (z 2 : ZMod Q) = 0 := congrArg (fun g : Group Q => g.2) hp
    obtain ⟨k, hk⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (z 2) Q).mp h2
    refine ⟨k, ?_⟩
    ext i
    fin_cases i <;> simp [kernelStep, h0, h1, hk, mul_comm]
  · rintro ⟨k, rfl⟩
    change projection Q (k • kernelStep Q) = 0
    simp only [map_zsmul, projection_kernelStep, zsmul_zero]

def representatives (Q : ℕ) (F : Finset (Group Q)) : Finset (Lattice 3) :=
  F.image (lift Q)

theorem lift_mem_representatives (Q : ℕ) {F : Finset (Group Q)}
    {f : Group Q} (hf : f ∈ F) : lift Q f ∈ representatives Q F :=
  Finset.mem_image_of_mem _ hf

theorem projection_mem_of_mem_representatives (Q : ℕ) [NeZero Q]
    {F : Finset (Group Q)} {u : Lattice 3} (hu : u ∈ representatives Q F) :
    projection Q u ∈ F := by
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hu
  simpa only [projection_lift] using hf

theorem projection_injOn_representatives (Q : ℕ) [NeZero Q]
    (F : Finset (Group Q)) :
    Set.InjOn (projection Q) (representatives Q F : Set (Lattice 3)) := by
  intro u hu v hv huv
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hv
  have hfg : f = g := by simpa only [projection_lift] using huv
  exact congrArg (lift Q) hfg

theorem projection_image_representatives (Q : ℕ) [NeZero Q]
    (F : Finset (Group Q)) :
    (representatives Q F).image (projection Q) = F := by
  ext f
  constructor
  · intro hf
    obtain ⟨u, hu, huf⟩ := Finset.mem_image.mp hf
    rw [← huf]
    exact projection_mem_of_mem_representatives Q hu
  · intro hf
    exact Finset.mem_image.mpr
      ⟨lift Q f, lift_mem_representatives Q hf, projection_lift Q f⟩

theorem zero_mem_representatives (Q : ℕ) {F : Finset (Group Q)}
    (hF : 0 ∈ F) : 0 ∈ representatives Q F := by
  simpa only [lift_zero] using lift_mem_representatives Q hF

theorem eq_zero_of_mem_representatives_mem_ker (Q : ℕ) [NeZero Q]
    {F : Finset (Group Q)} {u : Lattice 3}
    (hu : u ∈ representatives Q F) (hk : u ∈ (projection Q).ker) : u = 0 := by
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hu
  have hf0 : f = 0 := by
    simpa only [AddMonoidHom.mem_ker, projection_lift] using hk
  rw [hf0, lift_zero]

theorem kernelStep_not_mem_representatives (Q : ℕ) [NeZero Q]
    (F : Finset (Group Q)) : kernelStep Q ∉ representatives Q F := by
  intro h
  exact kernelStep_ne_zero Q
    (eq_zero_of_mem_representatives_mem_ker Q h (projection_kernelStep Q))

theorem preimage_tiles (Q : ℕ) [NeZero Q]
    {F : Finset (Group Q)} {A : Set (Group Q)} (h : Tiles F A) :
    Tiles (representatives Q F) ((projection Q) ⁻¹' A) := by
  rw [tiles_iff_unique_tile]
  intro x
  obtain ⟨f, hf, huniq⟩ := (tiles_iff_unique_tile.mp h) (projection Q x)
  refine ⟨⟨lift Q f, lift_mem_representatives Q f.property⟩, ?_, ?_⟩
  · change projection Q (x - lift Q f) ∈ A
    simpa only [map_sub, projection_lift] using hf
  · intro u hu
    have hpu : projection Q u ∈ F :=
      projection_mem_of_mem_representatives Q u.property
    have hp : projection Q x - projection Q u ∈ A := by
      simpa only [Set.mem_preimage, map_sub] using hu
    have he := huniq ⟨projection Q u, hpu⟩ hp
    apply Subtype.ext
    apply projection_injOn_representatives Q F u.property
      (lift_mem_representatives Q f.property)
    simpa only [projection_lift] using congrArg Subtype.val he

theorem period_preimage_of_mem_ker (Q : ℕ) (A : Set (Group Q))
    {k : Lattice 3} (hk : k ∈ (projection Q).ker) :
    Period ((projection Q) ⁻¹' A) k := by
  intro x
  change projection Q (x + k) ∈ A ↔ projection Q x ∈ A
  have hk' : projection Q k = 0 := hk
  simp only [map_add, hk', add_zero]

theorem period_preimage_kernelStep (Q : ℕ) (A : Set (Group Q)) :
    Period ((projection Q) ⁻¹' A) (kernelStep Q) :=
  period_preimage_of_mem_ker Q A (projection_kernelStep Q)

end CyclicQuotient
end PeriodicTilingThree

end OAI
