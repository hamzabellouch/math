import Mathlib
import OAI.Combinatorics.HoneycombCorridor.PotentialSupport
import OAI.Combinatorics.HoneycombCorridor.EulerRank

namespace OAI

noncomputable section

namespace PolynomialVacuumBridge.Corridor

noncomputable def extendOn {α : Type*} [DecidableEq α] (S : Finset α) (f : S → ℚ) : α →₀ ℚ :=
  Finsupp.onFinset S (fun a => if ha : a ∈ S then f ⟨a,ha⟩ else 0)
    (by intro a h; by_contra ha; simp [ha] at h)

@[simp] theorem extendOn_apply_mem {α : Type*} [DecidableEq α]
    (S : Finset α) (f : S → ℚ) (a : S) : extendOn S f a = f a := by
  simp [extendOn]

@[simp] theorem extendOn_apply_not_mem {α : Type*} [DecidableEq α]
    (S : Finset α) (f : S → ℚ) (a : α) (ha : a ∉ S) : extendOn S f a = 0 := by
  simp [extendOn,ha]

theorem extendOn_support {α : Type*} [DecidableEq α]
    (S : Finset α) (f : S → ℚ) : (extendOn S f).support ⊆ S := by
  intro a ha
  by_contra h
  exact (Finsupp.mem_support_iff.mp ha) (extendOn_apply_not_mem S f a h)

theorem extendOn_injective {α : Type*} [DecidableEq α] (S : Finset α) :
    Function.Injective (extendOn S) := by
  intro f g h
  funext a
  have he := congrArg (fun t : α →₀ ℚ => t a) h
  simpa using he

theorem extendOn_restrict {α : Type*} [DecidableEq α] (S : Finset α)
    (f : α →₀ ℚ) (h : f.support ⊆ S) : extendOn S (fun a => f a) = f := by
  ext a
  by_cases ha : a ∈ S
  · exact extendOn_apply_mem S (fun a => f a) ⟨a,ha⟩
  · rw [extendOn_apply_not_mem S _ a ha]
    by_contra hf
    exact ha (h (Finsupp.mem_support_iff.mpr (Ne.symm hf)))

noncomputable def rationalBoundary : (EdgeIndex →₀ ℚ) →+ (Vertex →₀ ℚ) :=
  Finsupp.liftAddHom fun e => Finsupp.singleAddHom (upEnd e) - Finsupp.singleAddHom (downEnd e)

@[simp] theorem rationalBoundary_single (e : EdgeIndex) (a : ℚ) :
    rationalBoundary (Finsupp.single e a) =
      Finsupp.single (upEnd e) a - Finsupp.single (downEnd e) a := by
  simp [rationalBoundary]

theorem rationalBoundary_up (q : EdgeIndex →₀ ℚ) (i j : ℤ) :
    rationalBoundary q (.up i j) = q ((i,j),0) + q ((i,j),1) + q ((i,j),2) := by
  classical
  induction q using Finsupp.induction_linear with
  | zero => simp
  | add q r hq hr => simp only [map_add,Finsupp.add_apply,hq,hr]; ring
  | single e a =>
      rcases e with ⟨⟨x,y⟩,k⟩
      fin_cases k <;>
        simp [rationalBoundary_single,upEnd,downEnd,neighbor,Finsupp.single_apply,eq_comm]

theorem rationalBoundary_down (q : EdgeIndex →₀ ℚ) (i j : ℤ) :
    rationalBoundary q (.down i j) =
      -(q ((i,j+1),0) + q ((i,j),1) + q ((i+1,j),2)) := by
  classical
  induction q using Finsupp.induction_linear with
  | zero => simp
  | add q r hq hr => simp only [map_add,Finsupp.add_apply,hq,hr]; ring
  | single e a =>
      rcases e with ⟨⟨x,y⟩,k⟩
      have hy : j = y - 1 ↔ y = j + 1 := by omega
      have hx : i = x - 1 ↔ x = i + 1 := by omega
      fin_cases k <;>
        simp [rationalBoundary_single,upEnd,downEnd,neighbor,Finsupp.single_apply,eq_comm,hy,hx]

theorem rationalBoundary_apply (q : EdgeIndex →₀ ℚ) (v : Vertex) :
    rationalBoundary q v = ∑ k : Fin 3, directedCurrent q (v,k) := by
  cases v <;> simp [rationalBoundary_up,rationalBoundary_down,Fin.sum_univ_succ,
    directedCurrent,dartSign,edgeOf] <;> ring

theorem rationalBoundary_eq_zero (q : EdgeIndex →₀ ℚ) :
    rationalBoundary q = 0 ↔ ConservedCurrent q := by
  simp only [ConservedCurrent,← rationalBoundary_apply,DFunLike.ext_iff,Finsupp.zero_apply]

noncomputable def incidenceMatrix (S : Finset FaceIndex) :
    Matrix (cellVertices S) (cellEdges S) ℚ :=
  fun v e => (if v.1 = upEnd e then 1 else 0) - (if v.1 = downEnd e then 1 else 0)

theorem cell_upEnd (S : Finset FaceIndex) (e : cellEdges S) : upEnd e ∈ cellVertices S := by
  apply edge_mem_vertex S (canonicalDart e)
  have h : edgeOf (canonicalDart e) = e := by
    rcases e with ⟨⟨⟨i,j⟩,k⟩,he⟩
    rfl
  rw [h]
  exact e.property

theorem cell_downEnd (S : Finset FaceIndex) (e : cellEdges S) : downEnd e ∈ cellVertices S := by
  apply edge_mem_neighbor S (canonicalDart e)
  have h : edgeOf (canonicalDart e) = e := by
    rcases e with ⟨⟨⟨i,j⟩,k⟩,he⟩
    rfl
  rw [h]
  exact e.property

theorem transpose_incidence_apply (S : Finset FaceIndex) (f : cellVertices S → ℚ)
    (e : cellEdges S) :
    (incidenceMatrix S).transpose.mulVec f e =
      f ⟨upEnd e,cell_upEnd S e⟩ - f ⟨downEnd e,cell_downEnd S e⟩ := by
  classical
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, incidenceMatrix, sub_mul,
    ite_mul, one_mul, zero_mul, Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_eq_single ⟨upEnd e,cell_upEnd S e⟩]
    · simp
    · intro b _ hb
      have h : b.1 ≠ upEnd e := fun h => hb (Subtype.ext h)
      simp [h]
    · simp
  · rw [Finset.sum_eq_single ⟨downEnd e,cell_downEnd S e⟩]
    · simp
    · intro b _ hb
      have h : b.1 ≠ downEnd e := fun h => hb (Subtype.ext h)
      simp [h]
    · simp

@[simp] theorem extendOn_add {α : Type*} [DecidableEq α] (S : Finset α)
    (f g : S → ℚ) : extendOn S (f + g) = extendOn S f + extendOn S g := by
  ext a
  by_cases ha : a ∈ S <;> simp [extendOn,ha]

@[simp] theorem extendOn_smul {α : Type*} [DecidableEq α] (S : Finset α)
    (c : ℚ) (f : S → ℚ) : extendOn S (c • f) = c • extendOn S f := by
  ext a
  by_cases ha : a ∈ S <;> simp [extendOn,ha]

theorem extendOn_eq_sum {α : Type*} [DecidableEq α] (S : Finset α) (f : S → ℚ) :
    extendOn S f = ∑ a : S, Finsupp.single a.1 (f a) := by
  ext a
  by_cases ha : a ∈ S
  · change extendOn S f (⟨a,ha⟩ : S) = _
    rw [extendOn_apply_mem,Finsupp.finsetSum_apply,Finset.sum_eq_single (⟨a,ha⟩ : S)]
    · simp
    · intro b _ hb
      have h : b.1 ≠ a := fun h => hb (Subtype.ext h)
      simp [h]
    · simp
  · rw [extendOn_apply_not_mem S f a ha,Finsupp.finsetSum_apply]
    symm
    apply Finset.sum_eq_zero
    intro b _
    have hb : b.1 ≠ a := fun h => ha (h ▸ b.property)
    simp [hb]

theorem incidence_apply (S : Finset FaceIndex) (q : cellEdges S → ℚ)
    (v : cellVertices S) :
    (incidenceMatrix S).mulVec q v = rationalBoundary (extendOn (cellEdges S) q) v := by
  rw [extendOn_eq_sum,map_sum,Finsupp.finsetSum_apply]
  simp only [Matrix.mulVec,dotProduct,incidenceMatrix,rationalBoundary_single,
    Finsupp.sub_apply,Finsupp.single_apply]
  apply Finset.sum_congr rfl
  intro e _
  simp only [sub_mul,ite_mul,one_mul,zero_mul,eq_comm]

theorem rationalBoundary_support_cells (S : Finset FaceIndex) (q : EdgeIndex →₀ ℚ)
    (hS : q.support ⊆ cellEdges S) : (rationalBoundary q).support ⊆ cellVertices S := by
  intro v hv
  by_contra hV
  apply (Finsupp.mem_support_iff.mp hv)
  rw [rationalBoundary_apply]
  apply Finset.sum_eq_zero
  intro k _
  have hz : q (edgeOf (v,k)) = 0 := by
    by_contra he
    exact hV (edge_mem_vertex S (v,k) (hS (Finsupp.mem_support_iff.mpr he)))
  simp [directedCurrent,hz]

theorem incidence_zero_iff (S : Finset FaceIndex) (q : cellEdges S → ℚ) :
    (incidenceMatrix S).mulVec q = 0 ↔ ConservedCurrent (extendOn (cellEdges S) q) := by
  rw [← rationalBoundary_eq_zero]
  constructor
  · intro h
    ext v
    by_cases hv : v ∈ cellVertices S
    · have he := congrFun h ⟨v,hv⟩
      simpa only [incidence_apply,Pi.zero_apply,Finsupp.zero_apply] using he
    · change rationalBoundary _ v = 0
      by_contra he
      exact hv (rationalBoundary_support_cells S _ (extendOn_support _ _)
        (Finsupp.mem_support_iff.mpr he))
  · intro h
    funext v
    rw [incidence_apply,h]
    rfl

theorem gradient_zero_off_cells (S : Finset FaceIndex) (r : FaceIndex →₀ ℚ)
    (hr : r.support ⊆ S) (e : EdgeIndex) (he : e ∉ cellEdges S) :
    faceGradient r e = 0 := by
  rw [mem_cellEdges,not_or] at he
  have hz (a : FaceIndex) (ha : a ∉ S) : r a = 0 := by
    by_contra h
    exact ha (hr (Finsupp.mem_support_iff.mpr h))
  simp [faceGradient,hz _ he.1,hz _ he.2]

noncomputable def cellFaceBoundary (S : Finset FaceIndex) :
    (S → ℚ) →ₗ[ℚ] (cellEdges S → ℚ) where
  toFun f e := faceGradient (extendOn S f) e
  map_add' f g := by
    funext e
    simp [extendOn_add,faceGradient]
    ring
  map_smul' c f := by
    funext e
    simp [extendOn_smul,faceGradient]
    ring

theorem extend_faceBoundary (S : Finset FaceIndex) (f : S → ℚ) :
    (extendOn (cellEdges S) (cellFaceBoundary S f) : EdgeIndex → ℚ) =
      faceGradient (extendOn S f) := by
  funext e
  by_cases he : e ∈ cellEdges S
  · exact extendOn_apply_mem _ _ ⟨e,he⟩
  · rw [extendOn_apply_not_mem _ _ _ he,
      gradient_zero_off_cells S _ (extendOn_support _ _) e he]

theorem cellFaceBoundary_injective (S : Finset FaceIndex) :
    Function.Injective (cellFaceBoundary S) := by
  intro f g h
  apply extendOn_injective S
  apply finite_gradient_injective
  rw [← extend_faceBoundary,← extend_faceBoundary,h]

theorem cellFaceBoundary_range (g : Germ) (w : List Bool)
    (hN : (traced g w).Nodup) (hc : terminalGerm g w = g)
    (p : FaceIndex →₀ ℤ) (hp : RepresentsFlow p (wordFlow g w)) (hpne : p ≠ 0) :
    (cellFaceBoundary p.support).range = (incidenceMatrix p.support).mulVecLin.ker := by
  ext q
  change (∃ f,cellFaceBoundary p.support f = q) ↔ (incidenceMatrix p.support).mulVec q = 0
  rw [incidence_zero_iff]
  constructor
  · rintro ⟨f,rfl⟩
    rw [extend_faceBoundary]
    exact gradient_conserved _
  · intro hq
    obtain ⟨r,hr⟩ := conserved_finite_potential _ hq
    have hS : r.support ⊆ p.support := by
      apply potential_supported_on_cycle_cells g w hN hc p hp hpne r
      intro e he
      rw [hr]
      exact extendOn_apply_not_mem _ _ _ he
    refine ⟨fun a => r a,?_⟩
    funext e
    change faceGradient (extendOn p.support (fun a => r a)) e = q e
    rw [extendOn_restrict _ r hS,hr]
    exact extendOn_apply_mem _ _ e

theorem represented_nonzero_edge_mem (S : Finset FaceIndex) (p : FaceIndex →₀ ℤ)
    (hS : p.support ⊆ S) (q : EdgeIndex →₀ ℤ) (hp : RepresentsFlow p q)
    (g : Germ) (hg : orientedFlow q g ≠ 0) : edgeOf g ∈ cellEdges S := by
  rw [edge_mem_around]
  have h := hp g
  by_contra hn
  simp only [not_or] at hn
  have hz (a : FaceIndex) (ha : a ∉ S) : p a = 0 := by
    by_contra h
    exact ha (hS (Finsupp.mem_support_iff.mpr h))
  rw [hz _ hn.1,hz _ hn.2,sub_self] at h
  exact hg h

theorem contour_outgoing_nonzero (q : EdgeIndex →₀ ℤ) (g : Germ) (b : Bool)
    (h : LocalContour q g b) : orientedFlow q (g.1,outgoingSlot g b) ≠ 0 := by
  have hk : outgoingSlot g b ≠ g.2 := by
    rcases g with ⟨v,k⟩
    fin_cases k <;> cases b <;> simp [outgoingSlot]
  rw [h (outgoingSlot g b)]
  simp [hk]

theorem contour_step_mem (p : FaceIndex →₀ ℤ) (q : EdgeIndex →₀ ℤ)
    (hp : RepresentsFlow p q) (g : Germ) (b : Bool) (h : LocalContour q g b) :
    edgeOf (g.1,outgoingSlot g b) ∈ cellEdges p.support := by
  exact represented_nonzero_edge_mem _ p (Finset.Subset.refl _) q hp _
    (contour_outgoing_nonzero q g b h)

theorem contour_flat_trace (p : FaceIndex →₀ ℤ) (q : EdgeIndex →₀ ℤ)
    (hp : RepresentsFlow p q) (f : Vertex → ℚ)
    (hf : ∀ e ∈ cellEdges p.support, f (upEnd e) = f (downEnd e))
    (g : Germ) (w : List Bool) (hw : WordContour q g w) :
    ∀ v ∈ traced g w, v ∈ cellVertices p.support ∧ f v = f g.1 := by
  induction w generalizing g with
  | nil => simp [traced]
  | cons b w ih =>
      have hE := contour_step_mem p q hp g b hw.1
      have hV := edge_mem_vertex _ _ hE
      have hs : f (advance g b).1 = f g.1 :=
        flat_along_dart _ f hf (g.1,outgoingSlot g b) hE
      simp only [traced,List.mem_cons]
      intro v hv
      rcases hv with rfl | hv
      · exact ⟨hV,rfl⟩
      · obtain ⟨hv',hf'⟩ := ih (advance g b) hw.2 v hv
        exact ⟨hv',hf'.trans hs⟩

theorem cycle_vertices_nonempty (g : Germ) (w : List Bool) (hne : w ≠ [])
    (hN : (traced g w).Nodup) (hc : terminalGerm g w = g)
    (p : FaceIndex →₀ ℤ) (hp : RepresentsFlow p (wordFlow g w)) :
    g.1 ∈ cellVertices p.support := by
  obtain ⟨b,w,rfl⟩ := List.exists_cons_of_ne_nil hne
  have h := (simple_closed_word_contour g (b::w) hN hc).1
  exact edge_mem_vertex _ (g.1,outgoingSlot g b) (contour_step_mem p _ hp g b h)

theorem transpose_incidence_kernel (g : Germ) (w : List Bool) (hne : w ≠ [])
    (hN : (traced g w).Nodup) (hc : terminalGerm g w = g)
    (p : FaceIndex →₀ ℤ) (hp : RepresentsFlow p (wordFlow g w)) :
    (incidenceMatrix p.support).transpose.mulVecLin.ker =
      Submodule.span ℚ {(1 : cellVertices p.support → ℚ)} := by
  have hg : g.1 ∈ cellVertices p.support := cycle_vertices_nonempty g w hne hN hc p hp
  ext f
  change (incidenceMatrix p.support).transpose.mulVec f = 0 ↔ _
  rw [Submodule.mem_span_singleton]
  constructor
  · intro h
    let fhat := extendOn (cellVertices p.support) f
    have hflat : ∀ e ∈ cellEdges p.support, fhat (upEnd e) = fhat (downEnd e) := by
      intro e he
      have heq := congrFun h ⟨e,he⟩
      rw [transpose_incidence_apply] at heq
      have h1 := cell_upEnd p.support (⟨e,he⟩ : cellEdges p.support)
      have h2 := cell_downEnd p.support (⟨e,he⟩ : cellEdges p.support)
      simpa only [fhat,extendOn,Finsupp.onFinset_apply,dite_eq_left h1,dite_eq_left h2] using
        sub_eq_zero.mp heq
    have htrace := contour_flat_trace p (wordFlow g w) hp fhat hflat g w
      (simple_closed_word_contour g w hN hc)
    let c : ℚ := fhat g.1
    let diff : Vertex →₀ ℚ := extendOn (cellVertices p.support) (fun a => f a - c)
    have hdiff (a : cellVertices p.support) : diff a = f a - c :=
      extendOn_apply_mem _ _ a
    have hd : diff = 0 := by
      apply cell_flat_zero_boundary g w hc p hp diff (extendOn_support _ _)
      · intro e he
        have h1 := cell_upEnd p.support (⟨e,he⟩ : cellEdges p.support)
        have h2 := cell_downEnd p.support (⟨e,he⟩ : cellEdges p.support)
        have he' := congrArg (fun x : ℚ => x-c) (hflat e he)
        simpa only [diff,fhat,extendOn,Finsupp.onFinset_apply,dite_eq_left h1,dite_eq_left h2] using he'
      · intro v hv
        obtain ⟨hv',he⟩ := htrace v hv
        change fhat v = c at he
        have he' : f ⟨v,hv'⟩ = c := by
          simpa only [fhat,extendOn,Finsupp.onFinset_apply,dite_eq_left hv'] using he
        simp only [diff,extendOn,Finsupp.onFinset_apply,dite_eq_left hv',he',sub_self]
    refine ⟨c,?_⟩
    funext a
    have he := congrArg (fun z : Vertex →₀ ℚ => z a) hd
    simp only [diff,extendOn,Finsupp.onFinset_apply,dite_eq_left a.property,Finsupp.zero_apply] at he
    simpa only [Pi.smul_apply,Pi.one_apply,smul_eq_mul,mul_one] using (sub_eq_zero.mp he).symm
  · rintro ⟨c,rfl⟩
    funext e
    rw [transpose_incidence_apply]
    simp

theorem simple_cycle_cell_euler (g : Germ) (w : List Bool) (hne : w ≠ [])
    (hN : (traced g w).Nodup) (hc : terminalGerm g w = g)
    (p : FaceIndex →₀ ℤ) (hp : RepresentsFlow p (wordFlow g w)) (hpne : p ≠ 0) :
    ((cellVertices p.support).card : ℤ) - (cellEdges p.support).card + p.support.card = 1 := by
  have : Nonempty (cellVertices p.support) :=
    ⟨⟨g.1,cycle_vertices_nonempty g w hne hN hc p hp⟩⟩
  simpa using cell_euler_of_exact (incidenceMatrix p.support) (cellFaceBoundary p.support)
    (cellFaceBoundary_injective _) (cellFaceBoundary_range g w hN hc p hp hpne)
    (transpose_incidence_kernel g w hne hN hc p hp)

end PolynomialVacuumBridge.Corridor

end

end OAI
