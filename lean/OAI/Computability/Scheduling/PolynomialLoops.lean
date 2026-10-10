import OAI.Computability.Scheduling.VolumeBounds

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16 u17 u18 u19 u20 u21 u22 u23 u24 u25 u26 u27

section
namespace ThreeMachine.StackCompiler
namespace Poly
variable {I : Type u1} {J : Type u2} {s : J → ℕ}
variable {α : I → Type u3} {β : I → Type u4} {γ : I → Type u5} [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)]
variable (idx : J → I) (xs : ∀ j, List (α (idx j))) (e : ∀ j, γ (idx j))

abbrev Pool := Σ j, {a : α (idx j) // a ∈ xs j}

theorem reparam {K : Type u6} {u f : K → ℕ} {d r : ℕ}
    (h : Poly u f d) (g : J → K) (hs : Poly s (fun j => u (g j)) r) :
    Poly s (fun j => f (g j)) (d*r) := by
  obtain ⟨C,hC⟩ := h
  apply of_le (fun j => hC (g j))
  have hN : Poly s (fun j => u (g j)+2) r := by
    simpa only [Nat.max_zero] using hs.add (const s 2)
  simpa only [Nat.zero_add,Nat.mul_comm] using (const s C).mul (hN.pow d)

theorem powerBase (s : J → ℕ) (C d : ℕ) : Poly s (fun j => C*(s j+2)^d) d := by
  poly_bound

omit [∀ i, Coding (α i)] [∀ i, Coding (γ i)] in
theorem volumeMap {f : ∀ i, α i × γ i → β i} {l v : ℕ}
    (hl : Poly s (fun j => (xs j).length) l)
    (hv : Poly (fun p : Pool idx xs => s p.1)
      (fun p => volume (f (idx p.1) (p.2.1,e p.1))) v) :
    Poly s (fun j => volume ((xs j).map (fun a => f (idx j) (a,e j)))) (l+v) := by
  obtain ⟨C,hC⟩ := hv
  apply volumeList (V := fun j => C*(s j+2)^v)
  · simpa only [List.length_map] using hl
  · exact powerBase s C v
  · intro j b hb
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
    exact hC ⟨j,⟨a,ha⟩⟩

theorem mapTime {f : ∀ i, α i × γ i → β i} (R : Uniform f) {l t vx ve v : ℕ}
    (hl : Poly s (fun j => (xs j).length) l)
    (ht : Poly (fun p : Pool idx xs => s p.1)
      (fun p => R.time (idx p.1) (p.2.1,e p.1)) t)
    (hx : Poly s (fun j => volume (xs j)) vx)
    (he : Poly s (fun j => volume (e j)) ve)
    (hv : Poly (fun p : Pool idx xs => s p.1)
      (fun p => volume (f (idx p.1) (p.2.1,e p.1))) v) :
    Poly s (fun j => R.map.time (idx j) (xs j,e j)) (l+Max.max t (Max.max vx (Max.max ve (l+v)))) := by
  have ho := volumeMap idx xs e hl hv
  obtain ⟨C,hC⟩ := ht
  have hT := powerBase s C t
  apply of_le (fun j => Uniform.time_map R (idx j) (xs j) (e j)
    (C*(s j+2)^t) (fun a ha => hC ⟨j,⟨a,ha⟩⟩))
  poly_bound

theorem filterTime {p : ∀ i, α i × γ i → Bool} (P : Uniform p) {l t vx ve : ℕ}
    (hl : Poly s (fun j => (xs j).length) l)
    (ht : Poly (fun q : Pool idx xs => s q.1)
      (fun q => P.time (idx q.1) (q.2.1,e q.1)) t)
    (hx : Poly s (fun j => volume (xs j)) vx)
    (he : Poly s (fun j => volume (e j)) ve) :
    Poly s (fun j => P.filter.time (idx j) (xs j,e j)) (l+Max.max t (Max.max vx ve)) := by
  obtain ⟨C,hC⟩ := ht
  have hT := powerBase s C t
  apply of_le (fun j => Uniform.time_filter P (idx j) (xs j) (e j)
    (C*(s j+2)^t) (fun a ha => hC ⟨j,⟨a,ha⟩⟩))
  poly_bound

theorem anyTime {p : ∀ i, α i × γ i → Bool} (P : Uniform p) {l t vx ve : ℕ}
    (hl : Poly s (fun j => (xs j).length) l)
    (ht : Poly (fun q : Pool idx xs => s q.1)
      (fun q => P.time (idx q.1) (q.2.1,e q.1)) t)
    (hx : Poly s (fun j => volume (xs j)) vx)
    (he : Poly s (fun j => volume (e j)) ve) :
    Poly s (fun j => P.any.time (idx j) (xs j,e j)) (l+Max.max t (Max.max vx ve)) := by
  obtain ⟨C,hC⟩ := ht
  have hT := powerBase s C t
  apply of_le (fun j => Uniform.time_any P (idx j) (xs j) (e j)
    (C*(s j+2)^t) (fun a ha => hC ⟨j,⟨a,ha⟩⟩))
  poly_bound

theorem allTime {p : ∀ i, α i × γ i → Bool} (P : Uniform p) {l t vx ve : ℕ}
    (hl : Poly s (fun j => (xs j).length) l)
    (ht : Poly (fun q : Pool idx xs => s q.1)
      (fun q => P.time (idx q.1) (q.2.1,e q.1)) t)
    (hx : Poly s (fun j => volume (xs j)) vx)
    (he : Poly s (fun j => volume (e j)) ve) :
    Poly s (fun j => P.all.time (idx j) (xs j,e j)) (l+Max.max t (Max.max vx ve)) := by
  obtain ⟨C,hC⟩ := ht
  have hT := powerBase s C t
  apply of_le (fun j => Uniform.time_all P (idx j) (xs j) (e j)
    (C*(s j+2)^t) (fun a ha => hC ⟨j,⟨a,ha⟩⟩))
  poly_bound

end Poly
end ThreeMachine.StackCompiler
namespace ThreeMachine.StackCompiler
namespace Poly
variable {J : Type u7} {s : J → ℕ} {d : ℕ}

theorem volumeFinRange {n : J → ℕ} (hn : Poly s n d) :
    Poly s (fun j => volume (List.finRange (n j))) (2*d) := by
  apply of_le (fun j => volume_finRange_le (n j))
  poly_bound

theorem finVal {n : J → ℕ} (hn : Poly s n d) (v : ∀ j, Fin (n j)) :
    Poly s (fun j => (v j).val) d := of_le (fun j => Nat.le_of_lt (v j).isLt) hn

theorem finsetCard {n : J → ℕ} (hn : Poly s n d) (a : ∀ j, Finset (Fin (n j))) :
    Poly s (fun j => (a j).card) d :=
  of_le (fun j => by simpa only [Fintype.card_fin] using Finset.card_le_univ (a j)) hn

variable {α : J → Type u8} {β : J → Type u9} [∀ j, Coding (α j)] [∀ j, Coding (β j)]

omit [∀ j, Coding (β j)] in
theorem lengthVolume (xs : ∀ j, List (α j)) (h : Poly s (fun j => volume (xs j)) d) :
    Poly s (fun j => (xs j).length) d := of_le (fun j => length_le_volume (xs j)) h

omit [∀ j, Coding (β j)] in
theorem volumePool (xs : ∀ j, List (α j)) (h : Poly s (fun j => volume (xs j)) d) :
    Poly (fun q : Pool _root_.id xs => s q.1) (fun q => volume q.2.1) d :=
  of_le (fun q => volume_mem_le q.2.2) (h.precomp Sigma.fst)

omit [∀ j, Coding (α j)] in
theorem volumeMapSimple (f : ∀ j, α j → β j) (xs : ∀ j, List (α j)) {l v : ℕ}
    (hl : Poly s (fun j => (xs j).length) l)
    (hv : Poly (fun q : Pool _root_.id xs => s q.1) (fun q => volume (f q.1 q.2.1)) v) :
    Poly s (fun j => volume ((xs j).map (f j))) (l+v) := by
  obtain ⟨C,hC⟩ := hv
  apply volumeList (V := fun j => C*(s j+2)^v)
  · simpa only [List.length_map] using hl
  · exact powerBase s C v
  · intro j b hb
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
    exact hC ⟨j,⟨a,ha⟩⟩

omit [∀ j, Coding (β j)] in
theorem volumeFilter (p : ∀ j, α j → Bool) (xs : ∀ j, List (α j))
    (h : Poly s (fun j => volume (xs j)) d) :
    Poly s (fun j => volume ((xs j).filter (p j))) d :=
  of_le (fun j => volume_filter_le (p j) (xs j)) h

end Poly
end ThreeMachine.StackCompiler

namespace ThreeMachine.StackCompiler.Poly
variable {J : Type u10} {s n : J → ℕ} {d : ℕ}
theorem lengthFinRange (hn : Poly s n d) :
    Poly s (fun j => (List.finRange (n j)).length) d := by simpa only [List.length_finRange] using hn

theorem lengthSort (a : ∀ j, Finset (Fin (n j)))
    (h : Poly s (fun j => (a j).card) d) :
    Poly s (fun j => ((a j).sort (· ≤ ·)).length) d := by simpa only [Finset.length_sort] using h

theorem lengthOfFn {α : J → Type u11} (a : ∀ j, Fin (n j) → α j) (hn : Poly s n d) :
    Poly s (fun j => (List.ofFn (a j)).length) d := by simpa only [List.length_ofFn] using hn
end ThreeMachine.StackCompiler.Poly

namespace ThreeMachine.StackCompiler.Poly
variable {I : Type u12} {J : Type u13} {α : I → Type u14} {β : I → Type u15} [∀ i, Coding (α i)] [∀ i, Coding (β i)]
theorem timeReparam {f : ∀ i, α i → β i} {R : Uniform f} {s : I → ℕ} {d : ℕ}
    (h : Poly (fun p : Σ i, α i => s p.1) (fun p => R.time p.1 p.2) d)
    (idx : J → I) (a : ∀ j, α (idx j)) {size : J → ℕ} {r : ℕ}
    (hn : Poly size (fun j => s (idx j)) r) :
    Poly size (fun j => R.time (idx j) (a j)) (d*r) :=
  h.reparam (fun j => ⟨idx j,a j⟩) hn
end ThreeMachine.StackCompiler.Poly
namespace ThreeMachine.StackCompiler.Poly
variable {J : Type u16} {s n : J → ℕ} {d v : ℕ}

def FinPool (n : J → ℕ) := Σ j, Fin (n j)

theorem volumeFunction {α : J → Type u17} [∀ j, Coding (α j)]
    (f : ∀ j, Fin (n j) → α j) (hn : Poly s n d)
    (hf : Poly (fun q : FinPool n => s q.1) (fun q => volume (f q.1 q.2)) v) :
    Poly s (fun j => volume (f j)) (d+v) := by
  obtain ⟨C,hC⟩ := hf
  apply of_le (g := fun j => 1+n j*(C*(s j+2)^v+1))
    (fun j => volume_function_le (f j) (C*(s j+2)^v) (fun a => hC ⟨j,a⟩))
  have : Poly s (fun j => C*(s j+2)^v) v := powerBase s C v
  simpa only [Nat.max_zero,Nat.zero_max] using (const s 1).add (hn.mul (this.add (const s 1)))

theorem iteNat (p : J → Prop) [∀ j, Decidable (p j)] {f g : J → ℕ} {d e : ℕ}
    (hf : Poly s f d) (hg : Poly s g e) : Poly s (fun j => if p j then f j else g j) (Max.max d e) :=
  of_le (g := fun j => Max.max (f j) (g j)) (fun j => by split <;> omega) (hf.max hg)

theorem natFunctionApply {f : ∀ j, Fin (n j) → ℕ} (a : ∀ j, Fin (n j))
    (hf : Poly s (fun j => volume (f j)) d) : Poly s (fun j => f j (a j)) d :=
  of_le (fun j => nat_function_apply_le (f j) (a j)) hf

end ThreeMachine.StackCompiler.Poly
namespace ThreeMachine.StackCompiler.Poly
variable {I : Type u18} {J : Type u19} {s : J → ℕ}
variable {α : I → Type u20} {β : I → Type u21} {γ : I → Type u22} [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)]
variable (idx : J → I) (xs : ∀ j, List (α (idx j))) (e : ∀ j, γ (idx j))

omit [∀ i, Coding (α i)] [∀ i, Coding (γ i)] in
theorem volumeFilterMap {f : ∀ i, α i × γ i → Option (β i)} {l v : ℕ}
    (hl : Poly s (fun j => (xs j).length) l)
    (hv : Poly (fun p : Pool idx xs => s p.1)
      (fun p => volume (f (idx p.1) (p.2.1,e p.1))) v) :
    Poly s (fun j => volume ((xs j).filterMap (fun a => f (idx j) (a,e j)))) (l+v) := by
  obtain ⟨C,hC⟩ := hv
  apply volumeList (V := fun j => C*(s j+2)^v)
  · exact of_le (fun j => List.length_filterMap_le _ _) hl
  · exact powerBase s C v
  · intro j b hb
    obtain ⟨a,ha,hb⟩ := List.mem_filterMap.mp hb
    have h := hC ⟨j,⟨a,ha⟩⟩
    dsimp only at h
    rw [hb,volume_some] at h
    omega

theorem filterMapTime {f : ∀ i, α i × γ i → Option (β i)} (R : Uniform f) {l t vx ve v : ℕ}
    (hl : Poly s (fun j => (xs j).length) l)
    (ht : Poly (fun p : Pool idx xs => s p.1)
      (fun p => R.time (idx p.1) (p.2.1,e p.1)) t)
    (hx : Poly s (fun j => volume (xs j)) vx)
    (he : Poly s (fun j => volume (e j)) ve)
    (hv : Poly (fun p : Pool idx xs => s p.1)
      (fun p => volume (f (idx p.1) (p.2.1,e p.1))) v) :
    Poly s (fun j => R.filterMap.time (idx j) (xs j,e j)) (l+Max.max t (Max.max vx (Max.max ve (l+v)))) := by
  have ho := volumeFilterMap idx xs e hl hv
  obtain ⟨C,hC⟩ := ht
  obtain ⟨D,hD⟩ := hv
  have hT := powerBase s C t
  have hV := powerBase s D v
  apply of_le (fun j => Uniform.time_filterMap R (idx j) (xs j) (e j)
    (C*(s j+2)^t) (D*(s j+2)^v) (fun a ha => hC ⟨j,⟨a,ha⟩⟩) (fun a ha => hD ⟨j,⟨a,ha⟩⟩))
  poly_bound

theorem firstResultTime {f : ∀ i, α i × γ i → Option (β i)} (R : Uniform f) {l t vx ve v : ℕ}
    (hl : Poly s (fun j => (xs j).length) l)
    (ht : Poly (fun p : Pool idx xs => s p.1)
      (fun p => R.time (idx p.1) (p.2.1,e p.1)) t)
    (hx : Poly s (fun j => volume (xs j)) vx)
    (he : Poly s (fun j => volume (e j)) ve)
    (hv : Poly (fun p : Pool idx xs => s p.1)
      (fun p => volume (f (idx p.1) (p.2.1,e p.1))) v) :
    Poly s (fun j => R.firstResult.time (idx j) (xs j,e j)) (l+Max.max t (Max.max vx (Max.max ve (l+v)))) := by
  obtain ⟨C,hC⟩ := ht
  obtain ⟨D,hD⟩ := hv
  have hT := powerBase s C t
  have hV := powerBase s D v
  apply of_le (fun j => Uniform.time_firstResult R (idx j) (xs j) (e j)
    (C*(s j+2)^t) (D*(s j+2)^v) (fun a ha => hC ⟨j,⟨a,ha⟩⟩) (fun a ha => hD ⟨j,⟨a,ha⟩⟩))
  poly_bound

end ThreeMachine.StackCompiler.Poly
namespace ThreeMachine.StackCompiler.Poly
variable {J : Type u23} {s : J → ℕ} {d e : ℕ} {α : J → Type u24} {β : J → Type u25}
variable [∀ j, Coding (α j)] [∀ j, Coding (β j)]
omit [∀ j, Coding (α j)] [∀ j, Coding (β j)] in
theorem lengthMap (f : ∀ j, α j → β j) {xs : ∀ j, List (α j)}
    (h : Poly s (fun j => (xs j).length) d) :
    Poly s (fun j => ((xs j).map (f j)).length) d := by simpa only [List.length_map] using h

omit [∀ j, Coding (α j)] [∀ j, Coding (β j)] in
theorem lengthProduct {xs : ∀ j, List (α j)} {ys : ∀ j, List (β j)}
    (hx : Poly s (fun j => (xs j).length) d) (hy : Poly s (fun j => (ys j).length) e) :
    Poly s (fun j => ((xs j).product (ys j)).length) (d+e) := by
  have h (j : J) : ((xs j).product (ys j)).length = (xs j).length*(ys j).length := by
    simp [List.product,List.length_flatMap]
  simpa only [h] using hx.mul hy

omit [∀ j, Coding (α j)] [∀ j, Coding (β j)] in
theorem lengthFilter (p : ∀ j, α j → Bool) {xs : ∀ j, List (α j)}
    (hx : Poly s (fun j => (xs j).length) d) :
    Poly s (fun j => ((xs j).filter (p j)).length) d := of_le (fun _ => List.length_filter_le _ _) hx

end ThreeMachine.StackCompiler.Poly

namespace ThreeMachine.StackCompiler.Poly
variable {J : Type u26} {s : J → ℕ} {α : J → Type u27} [∀ j, Coding (α j)]
abbrev ListPool (xs : ∀ j, List (α j)) := Σ j, {a : α j // a ∈ xs j}
theorem listVolume (xs : ∀ j, List (α j)) {l v : ℕ}
    (hl : Poly s (fun j => (xs j).length) l)
    (hv : Poly (fun q : ListPool xs => s q.1) (fun q => volume q.2.1) v) :
    Poly s (fun j => volume (xs j)) (l+v) := by
  obtain ⟨C,hC⟩ := hv
  exact volumeList hl (powerBase s C v) (fun j a ha => hC ⟨j,⟨a,ha⟩⟩)
end ThreeMachine.StackCompiler.Poly
end

end OAI
