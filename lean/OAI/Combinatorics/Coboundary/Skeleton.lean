import OAI.Combinatorics.Coboundary.Realization

namespace OAI

noncomputable section

/-!
Skeleton-weight identities and conversion of raw cosystolic estimates to the finite weighted norms.
-/

section
open scoped BigOperators
open Filter

namespace CoboundaryExpanders.Complex

local instance (X : Complex) (i : ℕ) : Fintype (X.Face i) := X.instFintypeFace i
local instance (X : Complex) (i : ℕ) : DecidableEq (X.Face i) := X.instDecidableEqFace i

end CoboundaryExpanders.Complex

namespace CoboundaryExpanders.FatLadders
variable {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
omit [Fintype V] [Fintype W] in
lemma delta_image (e : V ≃ W) (f : Finset W → k) (s : Finset V) :
    delta (fun t => f (t.image e)) s = delta f (s.image e) := by
  unfold delta
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro x hx
    change f ((s.erase x).image e) = _
    rw [Finset.image_erase e.injective]
  · exact fun _ _ _ _ h => e.injective h

lemma norm_image (e : V ≃ W) (w : Finset W → ℝ) (f : Finset W → k) (r : ℕ) :
    norm (fun t => w (t.image e)) r (fun t => f (t.image e)) = norm w r f := by
  unfold norm
  apply Finset.sum_bij (fun s _ => s.image e)
  · intro s hs
    simpa only [mem_level,Finset.card_image_of_injective _ e.injective] using hs
  · intro s hs t ht h
    exact Finset.image_injective e.injective h
  · intro s hs
    refine ⟨s.image e.symm,?_,?_⟩
    · simpa only [mem_level,Finset.card_image_of_injective _ e.symm.injective] using hs
    · simp only [Finset.image_image,Function.comp_def,Equiv.apply_symm_apply,Finset.image_id']
  · intro s hs
    rfl
end CoboundaryExpanders.FatLadders

namespace CoboundaryExpanders.Complex

section
local instance (X : Complex) (i : ℕ) : Fintype (X.Face i) := X.instFintypeFace i
local instance (X : Complex) (i : ℕ) : DecidableEq (X.Face i) := X.instDecidableEqFace i
variable (X : Complex)

def rawCochain (i : ℕ) (f : X.Cochain i) (s : Finset (Fin X.vertexCount)) : ZMod 2 :=
  if h : s ∈ X.facesOf i then f ⟨s,h⟩ else 0

def ofRaw (i : ℕ) (f : Finset (Fin X.vertexCount) → ZMod 2) : X.Cochain i := fun s => f s.val

@[simp] lemma ofRaw_rawCochain (i : ℕ) (f : X.Cochain i) :
    X.ofRaw i (X.rawCochain i f) = f := by
  ext s
  simp only [ofRaw,rawCochain,dite_eq_left s.property]

@[simp] lemma ofRaw_add (i : ℕ) (f g : Finset (Fin X.vertexCount) → ZMod 2) :
    X.ofRaw i (f+g) = X.ofRaw i f + X.ofRaw i g := rfl

lemma coboundary_ofRaw (i : ℕ) (f : Finset (Fin X.vertexCount) → ZMod 2) :
    X.coboundary i (X.ofRaw i f) = X.ofRaw (i+1) (FatLadders.delta f) := by
  ext t
  change (∑ s : X.Face i, if s.val ⊆ t.val then f s.val else 0) = ∑ x ∈ t.val, f (t.val.erase x)
  rw [←Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun x hx => (⟨t.val.erase x,(mem_facesOf X i _).mpr
    ⟨X.downward (face_mem t) (Finset.erase_subset _ _),by rw [Finset.card_erase_of_mem hx,face_card t]; omega⟩⟩ : X.Face i))
  · intro x hx
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact Finset.erase_subset _ _
  · intro x hx y hy hxy
    exact (Finset.erase_inj t.val hx).mp (congrArg Subtype.val hxy)
  · intro s hs
    have hst : s.val ⊆ t.val := (Finset.mem_filter.mp hs).2
    have hcard : (t.val \ s.val).card = 1 := by
      rw [Finset.card_sdiff_of_subset hst,face_card t,face_card s]; omega
    obtain ⟨x,hx,he⟩ := (Finset.covBy_iff_card_sdiff_eq_one.mpr ⟨hst,hcard⟩).exists_finset_erase
    exact ⟨x,hx,Subtype.ext he⟩
  · intro x hx
    rfl

lemma cofaceCount_zero_of_not_mem (n : ℕ) {s : Finset (Fin X.vertexCount)}
    (hs : s ∉ X.faces) : X.cofaceCount n s = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  obtain ⟨ht,hst⟩ := Finset.mem_filter.mp ht
  exact hs (X.downward ((mem_facesOf X n t).mp ht).1 hst)

lemma norm_ofRaw (n i : ℕ) (f : Finset (Fin X.vertexCount) → ZMod 2) :
    X.norm n i (X.ofRaw i f) =
      FatLadders.norm (fun s => (X.cofaceCount n s : ℝ)) (i+1) f /
        ((Nat.choose (n+1) (i+1) : ℝ)*(X.facesOf n).card) := by
  rw [norm]
  have he : (∑ s : X.Face i, if f s.val = 0 then (0:ℝ) else X.cofaceCount n s.val) =
      FatLadders.norm (fun s => (X.cofaceCount n s : ℝ)) (i+1) f := by
    rw [sum_face_eq X i (fun s => if f s = 0 then (0:ℝ) else X.cofaceCount n s)]
    unfold FatLadders.norm FatLadders.atom
    apply Finset.sum_subset
    · intro s hs
      exact FatLadders.mem_level.mpr ((mem_facesOf X i s).mp hs).2
    · intro s hs hnot
      have hsm : s ∉ X.faces := by
        intro hm
        exact hnot ((mem_facesOf X i s).mpr ⟨hm,FatLadders.mem_level.mp hs⟩)
      rw [X.cofaceCount_zero_of_not_mem n hsm]
      simp
  rw [←he,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s hs
  change (if f s.val ≠ 0 then X.weight n i s else 0) = _
  rw [weight_eq_cofaceCount]
  by_cases hf : f s.val = 0 <;> simp [hf]

lemma normalizer_pos {n i : ℕ} (hX : X.Pure n) (hi : i ≤ n) :
    0 < (Nat.choose (n+1) (i+1) : ℝ)*(X.facesOf n).card := by
  exact mul_pos (Nat.cast_pos.mpr (Nat.choose_pos (by omega))) (Nat.cast_pos.mpr hX.1.card_pos)

end

local instance (X : Complex) (i : ℕ) : Fintype (X.Face i) := X.instFintypeFace i
local instance (X : Complex) (i : ℕ) : DecidableEq (X.Face i) := X.instDecidableEqFace i
variable {X : Complex}
lemma raw_norm_eq_mul {n i : ℕ} (hX : X.Pure n) (hi : i ≤ n)
    (f : Finset (Fin X.vertexCount) → ZMod 2) :
    FatLadders.norm (fun s => (X.cofaceCount n s : ℝ)) (i+1) f =
      ((Nat.choose (n+1) (i+1) : ℝ)*(X.facesOf n).card)*X.norm n i (X.ofRaw i f) := by
  rw [X.norm_ofRaw]
  exact (mul_div_cancel₀ _ (X.normalizer_pos hX hi).ne').symm

theorem cosystolic_of_raw {n i : ℕ} (hX : X.Pure n) (hi : i < n) {K : ℝ} (hK : 0 < K)
    (hraw : ∀ f : Finset (Fin X.vertexCount) → ZMod 2, ∃ h,
      FatLadders.norm (fun s => (X.cofaceCount n s : ℝ)) (i+2) (FatLadders.delta (f+h)) = 0 ∧
      FatLadders.norm (fun s => (X.cofaceCount n s : ℝ)) (i+1) h ≤
        K*FatLadders.norm (fun s => (X.cofaceCount n s : ℝ)) (i+2) (FatLadders.delta f))
    (f : X.Cochain i) :
    (1/(K*2^(n+1))) * X.distance n i f (X.cocycles i) ≤ X.norm n (i+1) (X.coboundary i f) := by
  obtain ⟨h,hz,hb⟩ := hraw (X.rawCochain i f)
  have hdelta : X.coboundary i f = X.ofRaw (i+1) (FatLadders.delta (X.rawCochain i f)) := by
    simpa only [ofRaw_rawCochain] using X.coboundary_ofRaw i (X.rawCochain i f)
  have hz' : X.coboundary i (f+X.ofRaw i h) = 0 := by
    apply (norm_eq_zero_iff hX (by omega) _).mp
    rw [←X.ofRaw_rawCochain i f,←X.ofRaw_add,X.coboundary_ofRaw,X.norm_ofRaw]
    simp only [Nat.add_assoc,show 1+1=2 by rfl,hz,zero_div]
  have hn : X.norm n i (X.ofRaw i h) ≤ K*2^(n+1)*X.norm n (i+1) (X.coboundary i f) := by
    rw [raw_norm_eq_mul hX (by omega),raw_norm_eq_mul hX (by omega),←hdelta] at hb
    have hc0 : 1 ≤ (Nat.choose (n+1) (i+1) : ℝ) := by
      exact_mod_cast Nat.choose_pos (show i+1 ≤ n+1 by omega)
    have hc1 : (Nat.choose (n+1) (i+1+1) : ℝ) ≤ 2^(n+1) := by
      exact_mod_cast Nat.choose_le_two_pow (n+1) (i+1+1)
    have hbound : (Nat.choose (n+1) (i+1+1) : ℝ) ≤ 2^(n+1)*(Nat.choose (n+1) (i+1) : ℝ) :=
      hc1.trans (by nlinarith [show (0:ℝ) ≤ 2^(n+1) by positivity])
    apply (mul_le_mul_iff_right₀ (X.normalizer_pos (i:=i) hX (by omega))).mp
    apply hb.trans
    have hcnt : (0:ℝ) ≤ (X.facesOf n).card := Nat.cast_nonneg _
    have hx := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hbound hcnt) hK.le) (X.norm_nonneg n (i+1) (X.coboundary i f))
    nlinarith only [hx]
  have hd : X.distance n i f (X.cocycles i) ≤ X.norm n i (X.ofRaw i h) := by
    have hmem : f+X.ofRaw i h ∈ X.cocycles i := hz'
    have hh := X.distance_le_norm n i f hmem
    have he : f-(f+X.ofRaw i h) = X.ofRaw i h := by
      ext s
      simp only [Pi.sub_apply,Pi.add_apply,sub_add_cancel_left,CharTwo.neg_eq]
    rwa [he] at hh
  have hpos : 0 < K*2^(n+1) := mul_pos hK (by positivity)
  have hh := hd.trans hn
  apply (mul_le_mul_iff_right₀ hpos).mp
  convert hh using 1
  field_simp
end CoboundaryExpanders.Complex

namespace CoboundaryExpanders.FatLadders
variable {V W : Type} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]
lemma correction_image (e : V ≃ W) (wV : Finset V → ℝ) (wW : Finset W → ℝ)
    (hw : ∀ s,wW (s.image e) = wV s) (r : ℕ) (K : ℝ)
    (hh : ∀ f : Finset V → k, ∃ h,
      norm wV r (delta (f+h)) = 0 ∧ norm wV (r-1) h ≤ K*norm wV r (delta f)) :
    ∀ f : Finset W → k, ∃ h,
      norm wW r (delta (f+h)) = 0 ∧ norm wW (r-1) h ≤ K*norm wW r (delta f) := by
  intro f
  obtain ⟨h,hz,hb⟩ := hh (fun s => f (s.image e))
  let g : Finset W → k := fun s => h (s.image e.symm)
  have hg : (fun s => g (s.image e)) = h := by
    funext s
    simp only [g,Finset.image_image,Function.comp_def,Equiv.symm_apply_apply,Finset.image_id']
  have norm_transfer : ∀ r (F : Finset W → k),
      norm wV r (fun s => F (s.image e)) = norm wW r F := by
    intro r F
    have he : wV = fun s => wW (s.image e) := (funext hw).symm
    rw [he]
    exact norm_image e wW F r
  have hz' := norm_transfer r (delta (f+g))
  have hd : (fun s => delta (f+g) (s.image e)) = delta ((fun s => f (s.image e))+h) := by
    funext s
    rw [←delta_image e]
    congr 1
    funext t
    change f (t.image e)+g (t.image e) = f (t.image e)+h t
    rw [congrFun hg t]
  refine ⟨g,?_,?_⟩
  · rwa [←hz',hd]
  · rw [←norm_transfer (r-1) g,←norm_transfer r (delta f),hg]
    have hd' : (fun s => delta f (s.image e)) = delta (fun s => f (s.image e)) :=
      funext (fun s => (delta_image e f s).symm)
    rwa [hd']
end CoboundaryExpanders.FatLadders

namespace CoboundaryExpanders.Complex

section

local instance (X : Complex) (i : ℕ) : Fintype (X.Face i) := X.instFintypeFace i
local instance (X : Complex) (i : ℕ) : DecidableEq (X.Face i) := X.instDecidableEqFace i

end

local instance (X : Complex) (i : ℕ) : Fintype (X.Face i) := X.instFintypeFace i
local instance (X : Complex) (i : ℕ) : DecidableEq (X.Face i) := X.instDecidableEqFace i

open CategoryTheory

end CoboundaryExpanders.Complex

namespace CoboundaryExpanders.CosetConstruction

section
open CategoryTheory
local instance (X : CoboundaryExpanders.Complex) (i : ℕ) : Fintype (X.Face i) := X.instFintypeFace i
local instance (X : CoboundaryExpanders.Complex) (i : ℕ) : DecidableEq (X.Face i) := X.instDecidableEqFace i
variable {G : Type} [Group G] [Fintype G] {n : ℕ}
variable (H : Fin (n+1) → Subgroup G)

end

open InfiniteChains.FiniteWeights
variable {G : Type} [Group G] [Fintype G] {n : ℕ}
variable (H : Fin (n+1) → Subgroup G)

lemma labelled_cofaces (r : ℕ) (s : Finset (Vertex H)) :
    (complex H).cofaceCount r (s.image (labelEquiv H)) =
      cofaces (TypedCosetFaces.complex H) (r+1) s := by
  unfold Complex.cofaceCount cofaces
  symm
  apply Finset.card_bij (fun t _ => t.image (labelEquiv H))
  · intro t ht
    obtain ⟨ht,hst⟩ := Finset.mem_filter.mp ht
    obtain ⟨ht,hcard⟩ := (mem_level _ _ _).mp ht
    exact Finset.mem_filter.mpr ⟨(Complex.mem_facesOf _ _ _).mpr
      ⟨(labelled_mem_faces H t).mpr ht,by rwa [Finset.card_image_of_injective _ (labelEquiv H).injective]⟩,
      Finset.image_subset_image hst⟩
  · intro t ht u hu he
    exact Finset.image_injective (labelEquiv H).injective he
  · intro t ht
    obtain ⟨ht,hst⟩ := Finset.mem_filter.mp ht
    obtain ⟨ht,hcard⟩ := (Complex.mem_facesOf _ _ _).mp ht
    have he : (t.image (labelEquiv H).symm).image (labelEquiv H) = t := by
      simp only [Finset.image_image,Function.comp_def,Equiv.apply_symm_apply,Finset.image_id']
    refine ⟨t.image (labelEquiv H).symm,Finset.mem_filter.mpr ⟨(mem_level _ _ _).mpr ⟨?_,?_⟩,?_⟩,he⟩
    · apply (labelled_mem_faces H _).mp
      rwa [he]
    · rwa [Finset.card_image_of_injective _ (labelEquiv H).symm.injective]
    · apply (Finset.image_subset_image_iff (labelEquiv H).injective).mp
      rwa [he]

theorem cosystolic_of_typed_raw (i : ℕ) (hi : i < n) {K : ℝ} (hK : 0 < K)
    (hh : ∀ f : Finset (Vertex H) → ZMod 2, ∃ h,
      FatLadders.norm (fun s => (cofaces (TypedCosetFaces.complex H) (n+1) s : ℝ)) (i+2)
        (FatLadders.delta (f+h)) = 0 ∧
      FatLadders.norm (fun s => (cofaces (TypedCosetFaces.complex H) (n+1) s : ℝ)) (i+1) h ≤
        K*FatLadders.norm (fun s => (cofaces (TypedCosetFaces.complex H) (n+1) s : ℝ)) (i+2)
          (FatLadders.delta f)) :
    ∀ f : (complex H).Cochain i,
      (1/(K*2^(n+1))) * (complex H).distance n i f ((complex H).cocycles i) ≤
        (complex H).norm n (i+1) ((complex H).coboundary i f) := by
  apply Complex.cosystolic_of_raw (pure H) hi hK
  have he := FatLadders.correction_image (labelEquiv H)
    (fun s => (cofaces (TypedCosetFaces.complex H) (n+1) s : ℝ))
    (fun s => ((complex H).cofaceCount n s : ℝ))
    (fun s => by rw [labelled_cofaces]) (i+2) K
  simpa only [show i+2-1=i+1 by omega] using he hh
end CoboundaryExpanders.CosetConstruction

end

namespace CoboundaryExpanders.Complex

theorem skeleton_cosystolic_of_ambient {X : Complex} {i s n : ℕ}
    (hX : X.Pure n) (hi : i < s) (hs : s ≤ n) {M η : ℝ}
    (hM : 0 < M) (hη : 0 ≤ η)
    (hc : ∀ ρ : X.Face s, 1 ≤ (X.cofaceCount n ρ.val : ℝ) ∧
      (X.cofaceCount n ρ.val : ℝ) ≤ M)
    (hquant : ∀ f : X.Cochain i,
      η * X.distance n i f (X.cocycles i) ≤ X.norm n (i+1) (X.coboundary i f))
    (f : X.Cochain i) :
    (η/M) * X.distance s i f (X.cocycles i) ≤ X.norm s (i+1) (X.coboundary i f) := by
  have hZ : (X.cocycles i).Nonempty := ⟨0, by simp [cocycles]⟩
  have hdist := (skeleton_distance_comparison hX hi.le hs zero_lt_one hc f hZ).2
  have hnorm := (skeleton_norm_comparison hX hi hs zero_lt_one hc (X.coboundary i f)).1
  simp only [div_one] at hdist
  calc
    (η/M) * X.distance s i f (X.cocycles i) ≤
        (η/M) * (X.skeletonScale n s * X.distance n i f (X.cocycles i)) :=
      mul_le_mul_of_nonneg_left hdist (div_nonneg hη hM.le)
    _ = (X.skeletonScale n s/M) * (η * X.distance n i f (X.cocycles i)) := by ring
    _ ≤ (X.skeletonScale n s/M) * X.norm n (i+1) (X.coboundary i f) :=
      mul_le_mul_of_nonneg_left (hquant f) (div_nonneg (skeletonScale_pos hX hs).le hM.le)
    _ ≤ _ := hnorm
end CoboundaryExpanders.Complex

namespace CoboundaryExpanders.Construction
open InfiniteChains.FiniteWeights

theorem actual_uniform_cosystolic (n : ℕ) (hn : 2 ≤ n) :
    ∃ Q : ℕ, ∀ p : ℕ, ∀ _ : Fact p.Prime, Q < p → UniformCosystolic p n (by omega) := by
  obtain ⟨Q,K,hK,hraw⟩ := uniform_actual_raw_cosystolic n hn
  refine ⟨Q,?_⟩
  intro p hp hqp
  have hM : 0 < (localBound p n : ℝ) := by exact_mod_cast localBound_pos p n
  have heta : 0 < (1/(K*2^(n+1)) : ℝ) := by positivity
  refine ⟨(1/(K*2^(n+1)))/(localBound p n),div_pos heta hM,?_⟩
  intro m hm i hi
  apply (Complex.skeleton_cosystolic_iff hi _).mpr
  apply Complex.skeleton_cosystolic_of_ambient (finiteCosetComplex_pure p n (by omega) m) hi
    (by omega) hM heta.le (finiteCosetComplex_coface_bounds p n (by omega) m (n-1))
  let : Fintype (Gquot p (n+1) m) := Fintype.ofFinite _
  apply CosetConstruction.cosystolic_of_typed_raw (reducedLocalGroup p n (by omega) m) i (by omega) hK
  exact hraw p hp hqp m hm (i+2) (by omega)
end CoboundaryExpanders.Construction

end

end OAI
