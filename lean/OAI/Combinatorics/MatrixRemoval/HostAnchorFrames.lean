import OAI.Combinatorics.MatrixRemoval.Host
import OAI.Combinatorics.MatrixRemoval.AnchorFrames
import OAI.Combinatorics.MatrixRemoval.GuardedFrame

namespace OAI

/-!
Concrete selected-anchor frames for the canonical host.
The frame signatures follow from the actual host entry definition.
-/

noncomputable section
namespace Problem348.Construction

/-- A true first row role gives the exact first unit signature. -/
theorem host_row_role_zero {h : ℕ} (t : Mode h) (r : Position h)
    (hr : rowRole t 0 r) (v : Fin 64) (y : Fin (2 ^ h)) :
    host r (.inl (t,v,y)) = decide (v.val = 0) := by
  have hn : ¬ rowRole t 1 r := fun h₁ => rowRole_disjoint t r ⟨hr,h₁⟩
  cases r with
  | inl a => simp [rowRole] at hr
  | inr r => simp [host, hr, hn]

/-- A true second row role gives the exact second unit signature. -/
theorem host_row_role_one {h : ℕ} (t : Mode h) (r : Position h)
    (hr : rowRole t 1 r) (v : Fin 64) (y : Fin (2 ^ h)) :
    host r (.inl (t,v,y)) = decide (v.val = 1) := by
  have hn : ¬ rowRole t 0 r := fun h₀ => rowRole_disjoint t r ⟨h₀,hr⟩
  cases r with
  | inl a => simp [rowRole] at hr
  | inr r => simp [host, hr, hn]

/-- A true first column role gives the exact first unit signature. -/
theorem host_col_role_zero {h : ℕ} (t : Mode h) (c : Position h)
    (hc : colRole t 0 c) (u : Fin 64) (x : Fin (2 ^ h)) :
    host (.inl (t,u,x)) c = decide (u.val = 0) := by
  have hn : ¬ colRole t 1 c := fun h₁ => colRole_disjoint t c ⟨hc,h₁⟩
  cases c with
  | inl a => simp [colRole] at hc
  | inr c => simp [host, hc, hn]

/-- A true second column role gives the exact second unit signature. -/
theorem host_col_role_one {h : ℕ} (t : Mode h) (c : Position h)
    (hc : colRole t 1 c) (u : Fin 64) (x : Fin (2 ^ h)) :
    host (.inl (t,u,x)) c = decide (u.val = 1) := by
  have hn : ¬ colRole t 0 c := fun h₀ => colRole_disjoint t c ⟨h₀,hc⟩
  cases c with
  | inl a => simp [colRole] at hc
  | inr c => simp [host, hc, hn]

namespace SelectedAnchor

/-- Independent reindexings of the exact canonical raw host. -/
def matrix {h n : ℕ} (er ec : Position h ≃ Fin n) : BinaryMatrix n :=
  fun r c => host (er.symm r) (ec.symm c)

@[simp] theorem matrix_apply {h n : ℕ} (er ec : Position h ≃ Fin n)
    (r c : Position h) : matrix er ec (er r) (ec c) = host r c := by
  simp [matrix]

/-- One selected representative from each anchor group of a fixed mode. -/
def frame {h n : ℕ} (er ec : Position h ≃ Fin n) (t : Mode h)
    (a b : Fin 64 → Fin (2 ^ h))
    (hr : StrictMono (fun u => er (.inl (t,u,a u))))
    (hc : StrictMono (fun v => ec (.inl (t,v,b v)))) :
    GuardedPath.AnchorFrame n where
  rows := ⟨fun u => er (.inl (t,u,a u)), hr⟩
  cols := ⟨fun v => ec (.inl (t,v,b v)), hc⟩

/-- The actual host roles and the row/column order comparisons give a valid
selected frame. No body entry is required or constrained. -/
theorem frame_valid {h n : ℕ} (er ec : Position h ≃ Fin n) (t : Mode h)
    (a b : Fin 64 → Fin (2 ^ h))
    (hr : StrictMono (fun u => er (.inl (t,u,a u))))
    (hc : StrictMono (fun v => ec (.inl (t,v,b v))))
    (r₀ r₁ c₀ c₁ : Position h)
    (hr₀ : rowRole t 0 r₀) (hr₁ : rowRole t 1 r₁)
    (hc₀ : colRole t 0 c₀) (hc₁ : colRole t 1 c₁)
    (hbeforeR : ∀ u, er (.inl (t,u,a u)) < er r₀)
    (hrows : er r₀ < er r₁)
    (hbeforeC : ∀ v, ec (.inl (t,v,b v)) < ec c₀)
    (hcols : ec c₀ < ec c₁) :
    (frame er ec t a b hr hc).Valid (matrix er ec)
      (er r₀) (er r₁) (ec c₀) (ec c₁) := by
  refine ⟨hbeforeR, hrows, hbeforeC, hcols, ?_, ?_, ?_, ?_, ?_⟩
  · intro u v
    exact (matrix_apply er ec _ _).trans (host_anchor_same t u v (a u) (b v))
  · intro v
    exact (matrix_apply er ec _ _).trans (host_row_role_zero t r₀ hr₀ v (b v))
  · intro v
    exact (matrix_apply er ec _ _).trans (host_row_role_one t r₁ hr₁ v (b v))
  · intro u
    exact (matrix_apply er ec _ _).trans (host_col_role_zero t c₀ hc₀ u (a u))
  · intro u
    exact (matrix_apply er ec _ _).trans (host_col_role_one t c₁ hc₁ u (a u))

end SelectedAnchor
end Problem348.Construction

end

end OAI
