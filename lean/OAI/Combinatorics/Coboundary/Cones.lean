import OAI.Combinatorics.Coboundary.Chains

namespace OAI

noncomputable section

/-!
Quantitative chain cones, face-model transport, relabeling, and exactness under retractions.
-/

section
open scoped BigOperators

namespace CoboundaryExpanders.InfiniteChains.Cone
open Attachment
variable {V W : Type} [DecidableEq V] [DecidableEq W]

omit [DecidableEq V] in
lemma twice (c : Raw V) : c + c = 0 := by
  ext s
  exact CharTwo.add_self_eq_zero _

def size (c : Raw V) : ℕ := c.support.card

omit [DecidableEq V] in
@[simp] lemma size_zero : size (0 : Raw V) = 0 := by simp [size]

lemma size_add_le (c d : Raw V) : size (c+d) ≤ size c + size d :=
  (Finset.card_le_card Finsupp.support_add).trans (Finset.card_union_le _ _)

omit [DecidableEq V] in
lemma size_smul_le (a : k) (c : Raw V) : size (a • c) ≤ size c :=
  Finset.card_le_card Finsupp.support_smul

omit [DecidableEq V] in
lemma size_single_le (s : Finset V) (a : k) : size (Finsupp.single s a) ≤ 1 := by
  exact (Finset.card_le_card Finsupp.support_single_subset).trans (by simp)

lemma size_sum_le {ι : Type*} (S : Finset ι) (c : ι → Raw V) :
    size (∑ i ∈ S, c i) ≤ ∑ i ∈ S, size (c i) :=
  (Finset.card_le_card Finsupp.support_finsetSum).trans Finset.card_biUnion_le

omit [DecidableEq V] in
lemma size_map_le (T : Raw V →ₗ[k] Raw W) (P : Set (Finset V)) (C : ℕ)
    (hT : ∀ s ∈ P, size (T (Finsupp.single s 1)) ≤ C)
    (c : Raw V) (hc : c ∈ supported P) : size (T c) ≤ C * size c := by
  conv_lhs => rw [← Finsupp.sum_single c, Finsupp.sum, map_sum]
  calc
    size (∑ s ∈ c.support, T (Finsupp.single s (c s))) ≤
        ∑ s ∈ c.support, size (T (Finsupp.single s (c s))) := size_sum_le _ _
    _ ≤ ∑ _s ∈ c.support, C := by
      apply Finset.sum_le_sum
      intro s hs
      have he : Finsupp.single s (c s) = c s • Finsupp.single s (1 : k) := by simp
      rw [he, map_smul]
      exact (size_smul_le _ _).trans
        (hT s ((mem_supported P c).mp hc s (Finsupp.mem_support_iff.mp hs)))
    _ = C * size c := by simp [size, Nat.mul_comm]

lemma size_rawCone_le (a : V) (c : Raw V) : size (rawCone a c) ≤ size c := by
  have h := size_map_le (rawCone a) Set.univ 1 (fun s _ => by
    rw [rawCone_single]
    split_ifs
    · simp
    · exact size_single_le _ _) c (by rw [mem_supported]; simp)
  simpa using h

lemma rawCone_supported (a : V) (P Q : Set (Finset V))
    (h : ∀ s ∈ P, a ∉ s → insert a s ∈ Q)
    (c : Raw V) (hc : c ∈ supported P) : rawCone a c ∈ supported Q := by
  apply map_supported _ P Q _ c hc
  intro s hs r
  rw [rawCone_single]
  split_ifs with ha
  · exact Submodule.zero_mem _
  · exact single_mem_supported (h s hs ha) r

lemma rawCone_graded (a : V) (P Q : Set (Finset V)) (n : ℕ)
    (h : ∀ s ∈ P, a ∉ s → insert a s ∈ Q)
    (c : Raw V) (hc : c ∈ supported (graded P n)) :
    rawCone a c ∈ supported (graded Q (n+1)) := by
  apply rawCone_supported a (graded P n) (graded Q (n+1)) _ c hc
  intro s hs ha
  exact ⟨h s hs.1 ha, by rw [Finset.card_insert_of_notMem ha, hs.2]⟩

noncomputable def carrierFill (apex : Finset V → V) (s : Finset V) : Raw V :=
  rawCone (apex s) (Finsupp.single s 1 + ∑ v : s, carrierFill apex (s.erase v.val))
termination_by s.card
decreasing_by exact Finset.card_erase_lt_of_mem v.property

lemma carrierFill_eq (apex : Finset V → V) (s : Finset V) :
    carrierFill apex s = rawCone (apex s)
      (Finsupp.single s 1 + ∑ v ∈ s, carrierFill apex (s.erase v)) := by
  rw [carrierFill]
  congr 2
  exact Finset.sum_coe_sort s (fun v => carrierFill apex (s.erase v))

noncomputable def carrierMap (apex : Finset V → V) : Raw V →ₗ[k] Raw V :=
  Finsupp.linearCombination k (carrierFill apex)

@[simp] lemma carrierMap_single (apex : Finset V → V) (s : Finset V) (a : k) :
    carrierMap apex (Finsupp.single s a) = a • carrierFill apex s := by
  simp [carrierMap]

lemma boundary_carrierFill (apex : Finset V → V) (s : Finset V) :
    rawBoundary (carrierFill apex s) =
      Finsupp.single s 1 + ∑ v ∈ s, carrierFill apex (s.erase v) := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    have hdd := LinearMap.congr_fun (rawBoundary_squared (V := V)) (Finsupp.single s 1)
    have hz := congrArg (carrierMap apex) hdd
    simp only [LinearMap.comp_apply, LinearMap.zero_apply, rawBoundary_single,
      map_sum, carrierMap_single, one_smul, map_zero] at hz
    have he : rawBoundary (∑ v ∈ s, carrierFill apex (s.erase v)) = rawBoundary (Finsupp.single s 1) := by
      rw [map_sum]
      trans ∑ v ∈ s, (Finsupp.single (s.erase v) 1 + ∑ w ∈ s.erase v,
          carrierFill apex ((s.erase v).erase w))
      · apply Finset.sum_congr rfl
        intro v hv
        exact ih (s.erase v) (Finset.erase_ssubset hv)
      · rw [Finset.sum_add_distrib, hz, add_zero, rawBoundary_single]
    have hcycle : rawBoundary (Finsupp.single s 1 + ∑ v ∈ s,
        carrierFill apex (s.erase v)) = 0 := by
      rw [map_add, he, twice]
    rw [carrierFill_eq]
    have h := LinearMap.congr_fun (raw_contraction (apex s))
      (Finsupp.single s 1 + ∑ v ∈ s, carrierFill apex (s.erase v))
    simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
      hcycle, map_zero, add_zero] using h

lemma carrierMap_contraction (apex : Finset V → V) :
    rawBoundary.comp (carrierMap apex) + (carrierMap apex).comp rawBoundary = LinearMap.id := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext
  intro a
  simp only [LinearMap.add_apply, LinearMap.comp_apply, Finsupp.lsingle_apply, carrierMap_single,
    map_smul, boundary_carrierFill, rawBoundary_single, map_sum, LinearMap.id_apply]
  rw [smul_add, Finset.smul_sum]
  have h : (∑ v ∈ s, a • carrierFill apex (s.erase v)) +
      (∑ v ∈ s, a • carrierFill apex (s.erase v)) = 0 := twice _
  rw [add_assoc, h, add_zero]
  simp

def carrierBound : ℕ → ℕ
  | 0 => 1
  | n+1 => 1 + (n+1)*carrierBound n

lemma carrierFill_size (apex : Finset V → V) (s : Finset V) :
    size (carrierFill apex s) ≤ carrierBound s.card := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    rw [carrierFill_eq]
    calc
      size (rawCone (apex s) _) ≤ size (Finsupp.single s 1 +
          ∑ v ∈ s, carrierFill apex (s.erase v)) := size_rawCone_le _ _
      _ ≤ 1 + ∑ v ∈ s, size (carrierFill apex (s.erase v)) :=
        (size_add_le _ _).trans (Nat.add_le_add (size_single_le _ _) (size_sum_le _ _))
      _ ≤ 1 + s.card * carrierBound (s.card-1) := by
        apply Nat.add_le_add_left
        calc
          (∑ v ∈ s, size (carrierFill apex (s.erase v))) ≤
              ∑ _v ∈ s, carrierBound (s.card-1) := by
            apply Finset.sum_le_sum
            intro v hv
            simpa only [Finset.card_erase_of_mem hv] using ih (s.erase v) (Finset.erase_ssubset hv)
          _ = _ := by simp
      _ = carrierBound s.card := by
        cases he : s.card with
        | zero => simp [carrierBound]
        | succ n => simp [carrierBound]

lemma carrierFill_supported (X : CoboundaryExpanders.InfiniteChains.Complex V) (C : Finset V → Set (Finset V))
    (apex : Finset V → V)
    (hself : ∀ s ∈ X.faces, s ∈ C s)
    (hmono : ∀ s ∈ X.faces, ∀ t ⊆ s, C t ⊆ C s)
    (hcone : ∀ s ∈ X.faces, ∀ t ∈ C s, insert (apex s) t ∈ C s)
    (s : Finset V) (hs : s ∈ X.faces) :
    carrierFill apex s ∈ supported (graded (C s) (s.card+1)) := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    rw [carrierFill_eq]
    apply rawCone_graded (apex s) (C s) (C s) s.card
      (fun t ht _ => hcone s hs t ht)
    apply Submodule.add_mem
    · exact single_mem_supported (P := graded (C s) s.card) ⟨hself s hs, rfl⟩ _
    · apply Submodule.sum_mem
      intro v hv
      have hi := ih (s.erase v) (Finset.erase_ssubset hv)
        (X.downward hs (Finset.erase_subset _ _))
      apply supported_mono (P := graded (C (s.erase v)) ((s.erase v).card+1))
        (Q := graded (C s) s.card) ?_ hi
      intro t ht
      refine ⟨hmono s hs _ (Finset.erase_subset _ _) ht.1, ?_⟩
      have htcard := ht.2
      rw [Finset.card_erase_of_mem hv] at htcard
      have hpos := Finset.card_pos.mpr ⟨v, hv⟩
      omega

def link (v : V) : Raw V →ₗ[k] Raw V :=
  Finsupp.linearCombination k (fun s =>
    if v ∈ s then Finsupp.single (s.erase v) 1 else 0)

@[simp] lemma link_single (v : V) (s : Finset V) (a : k) :
    link v (Finsupp.single s a) =
      if v ∈ s then Finsupp.single (s.erase v) a else 0 := by
  by_cases h : v ∈ s <;> simp [link, h]

def without (v : V) : Raw V →ₗ[k] Raw V :=
  Finsupp.linearCombination k (fun s =>
    if v ∈ s then 0 else Finsupp.single s 1)

@[simp] lemma without_single (v : V) (s : Finset V) (a : k) :
    without v (Finsupp.single s a) = if v ∈ s then 0 else Finsupp.single s a := by
  by_cases h : v ∈ s <;> simp [without, h]

lemma cone_link_without (v : V) (c : Raw V) :
    rawCone v (link v c) + without v c = c := by
  have h : (rawCone v).comp (link v) + without v = LinearMap.id := by
    apply Finsupp.lhom_ext'
    intro s
    apply LinearMap.ext
    intro a
    simp only [LinearMap.add_apply, LinearMap.comp_apply, Finsupp.lsingle_apply,
      link_single, without_single, LinearMap.id_apply]
    by_cases hv : v ∈ s
    · simp [hv, Finset.insert_erase hv]
    · simp [hv]
  exact LinearMap.congr_fun h c

lemma link_boundary (v : V) :
    (link v).comp rawBoundary = rawBoundary.comp (link v) := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext
  intro a
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, rawBoundary_single, map_sum,
    link_single]
  by_cases hv : v ∈ s
  · rw [ite_eq_left hv, rawBoundary_single]
    rw [← Finset.sum_erase_add _ _ hv]
    simp only [Finset.mem_erase, ne_eq, not_true_eq_false, false_and, ite_false, add_zero]
    apply Finset.sum_congr rfl
    intro w hw
    have hwv := (Finset.mem_erase.mp hw).1
    rw [ite_eq_left ⟨Ne.symm hwv, hv⟩, Finset.erase_right_comm]
  · rw [ite_eq_right hv, map_zero]
    apply Finset.sum_eq_zero
    intro w hw
    exact ite_eq_right (fun h => hv (Finset.mem_of_mem_erase h))

lemma link_cycle (v : V) (c : Raw V) (hc : rawBoundary c = 0) :
    rawBoundary (link v c) = 0 := by
  have h := LinearMap.congr_fun (link_boundary v) c
  simpa [hc] using h.symm

lemma link_supported (v : V) (P Q : Set (Finset V))
    (h : ∀ s ∈ P, v ∈ s → s.erase v ∈ Q)
    (c : Raw V) (hc : c ∈ supported P) : link v c ∈ supported Q := by
  apply map_supported _ P Q _ c hc
  intro s hs a
  rw [link_single]
  split_ifs with hv
  · exact single_mem_supported (h s hs hv) a
  · exact Submodule.zero_mem _

lemma link_graded (v : V) (P Q : Set (Finset V)) (n : ℕ)
    (h : ∀ s ∈ P, v ∈ s → s.erase v ∈ Q)
    (c : Raw V) (hc : c ∈ supported (graded P (n+1))) :
    link v c ∈ supported (graded Q n) := by
  apply link_supported v (graded P (n+1)) (graded Q n) _ c hc
  intro s hs hv
  exact ⟨h s hs.1 hv, by rw [Finset.card_erase_of_mem hv, hs.2]; omega⟩

lemma without_supported (v : V) (P : Set (Finset V))
    (c : Raw V) (hc : c ∈ supported P) :
    without v c ∈ supported {s | s ∈ P ∧ v ∉ s} := by
  apply map_supported _ P _ _ c hc
  intro s hs a
  rw [without_single]
  split_ifs with hv
  · exact Submodule.zero_mem _
  · exact single_mem_supported (P := {s | s ∈ P ∧ v ∉ s}) ⟨hs, hv⟩ a

lemma link_size (v : V) (c : Raw V) : size (link v c) ≤ size c := by
  have h := size_map_le (link v) Set.univ 1 (fun s _ => by
    rw [link_single]
    split_ifs
    · exact size_single_le _ _
    · simp) c (by rw [mem_supported]; simp)
  simpa using h

lemma without_size (v : V) (c : Raw V) : size (without v c) ≤ size c := by
  have h := size_map_le (without v) Set.univ 1 (fun s _ => by
    rw [without_single]
    split_ifs
    · simp
    · exact size_single_le _ _) c (by rw [mem_supported]; simp)
  simpa using h

lemma elimination_identity (v : V) (c b : Raw V) (hb : rawBoundary b = link v c) :
    rawBoundary (rawCone v b) + (without v c + b) = c := by
  have h := LinearMap.congr_fun (raw_contraction v) b
  have he : rawBoundary (rawCone v b) + rawCone v (link v c) = b := by
    simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply, hb] using h
  have he' : rawBoundary (rawCone v b) = b + rawCone v (link v c) := by
    calc
      rawBoundary (rawCone v b) = rawBoundary (rawCone v b) +
          (rawCone v (link v c) + rawCone v (link v c)) := by rw [twice, add_zero]
      _ = b + rawCone v (link v c) := by rw [← add_assoc, he]
  rw [he']
  calc
    b + rawCone v (link v c) + (without v c + b) =
        (rawCone v (link v c) + without v c) + (b+b) := by ac_rfl
    _ = c := by rw [twice, add_zero, cone_link_without]

lemma elimination_cycle (v : V) (c b : Raw V) (hc : rawBoundary c = 0)
    (hb : rawBoundary b = link v c) : rawBoundary (without v c + b) = 0 := by
  have he := congrArg rawBoundary (elimination_identity v c b hb)
  have hdd := LinearMap.congr_fun (rawBoundary_squared (V := V)) (rawCone v b)
  have hdd' : rawBoundary (rawBoundary (rawCone v b)) = 0 := hdd
  simpa only [map_add, hdd', zero_add, hc] using he

lemma boundary_single_size (s : Finset V) (a : k) :
    size (rawBoundary (Finsupp.single s a)) ≤ s.card := by
  rw [rawBoundary_single]
  calc
    size (∑ v ∈ s, Finsupp.single (s.erase v) a) ≤
        ∑ v ∈ s, size (Finsupp.single (s.erase v) a) := size_sum_le _ _
    _ ≤ ∑ _v ∈ s, 1 := Finset.sum_le_sum (fun _ _ => size_single_le _ _)
    _ = s.card := by simp

omit [DecidableEq V] [DecidableEq W] in
lemma linear_eq_on_supported (A B : Raw V →ₗ[k] Raw W) (P : Set (Finset V))
    (h : ∀ s ∈ P, A (Finsupp.single s 1) = B (Finsupp.single s 1))
    (c : Raw V) (hc : c ∈ supported P) : A c = B c := by
  conv_lhs => rw [← Finsupp.sum_single c, Finsupp.sum, map_sum]
  conv_rhs => rw [← Finsupp.sum_single c, Finsupp.sum, map_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have he : Finsupp.single s (c s) = c s • Finsupp.single s (1 : k) := by simp
  rw [he, map_smul, map_smul,
    h s ((mem_supported P c).mp hc s (Finsupp.mem_support_iff.mp hs))]

structure BoundedCone (X : CoboundaryExpanders.InfiniteChains.Complex V) (n R : ℕ) where
  hom : Raw V →ₗ[k] Raw V
  support : ∀ s ∈ X.faces, s.card ≤ n →
    hom (Finsupp.single s 1) ∈ supported (graded X.faces (s.card+1))
  contraction : ∀ s ∈ X.faces, s.card ≤ n →
    rawBoundary (hom (Finsupp.single s 1)) + hom (rawBoundary (Finsupp.single s 1)) =
      Finsupp.single s 1
  bound : ∀ s ∈ X.faces, s.card ≤ n → size (hom (Finsupp.single s 1)) ≤ R

namespace BoundedCone
variable {X : CoboundaryExpanders.InfiniteChains.Complex V} {n R : ℕ} (H : BoundedCone X n R)

lemma map_graded (r : ℕ) (hr : r ≤ n) (c : Raw V)
    (hc : c ∈ supported (graded X.faces r)) :
    H.hom c ∈ supported (graded X.faces (r+1)) := by
  apply map_supported _ (graded X.faces r) _ _ c hc
  intro s hs a
  have he : Finsupp.single s a = a • Finsupp.single s (1 : k) := by simp
  rw [he, map_smul]
  apply Submodule.smul_mem
  have h := H.support s hs.1 (hs.2.trans_le hr)
  simpa only [hs.2] using h

lemma contraction_apply (r : ℕ) (hr : r ≤ n) (c : Raw V)
    (hc : c ∈ supported (graded X.faces r)) :
    rawBoundary (H.hom c) + H.hom (rawBoundary c) = c := by
  apply linear_eq_on_supported
    (rawBoundary.comp H.hom + H.hom.comp rawBoundary) LinearMap.id
    (graded X.faces r) _ c hc
  intro s hs
  exact H.contraction s hs.1 (hs.2.trans_le hr)

lemma size_apply (r : ℕ) (hr : r ≤ n) (c : Raw V)
    (hc : c ∈ supported (graded X.faces r)) : size (H.hom c) ≤ R * size c :=
  size_map_le H.hom (graded X.faces r) R
    (fun s hs => H.bound s hs.1 (hs.2.trans_le hr)) c hc

lemma fills (r : ℕ) (hr : r ≤ n) (c : Raw V)
    (hc : c ∈ supported (graded X.faces r)) (hz : rawBoundary c = 0) :
    rawBoundary (H.hom c) = c := by
  simpa only [hz, map_zero, add_zero] using H.contraction_apply r hr c hc

include H in
lemma exactIn (r : ℕ) (hr : r ≤ n) : ExactIn X.faces r := by
  intro c hc hz
  exact ⟨H.hom c, H.map_graded r hr c hc, H.fills r hr c hc hz⟩

lemma newCycle_supported (s : Finset V) (hs : s ∈ X.faces) (hr : s.card = n+1) :
    Finsupp.single s 1 + H.hom (rawBoundary (Finsupp.single s 1)) ∈
      supported (graded X.faces (n+1)) := by
  apply Submodule.add_mem
  · exact single_mem_supported (P := graded X.faces (n+1)) ⟨hs, hr⟩ _
  · apply H.map_graded n le_rfl
    apply boundary_graded X.faces (fun {_ _} hs h => X.downward hs h) n
    exact single_mem_supported (P := graded X.faces (n+1)) ⟨hs, hr⟩ _

lemma newCycle_cycle (s : Finset V) (hs : s ∈ X.faces) (hr : s.card = n+1) :
    rawBoundary (Finsupp.single s 1 + H.hom (rawBoundary (Finsupp.single s 1))) = 0 := by
  have hb : rawBoundary (Finsupp.single s 1) ∈ supported (graded X.faces n) := by
    apply boundary_graded X.faces (fun {_ _} hs h => X.downward hs h) n
    exact single_mem_supported (P := graded X.faces (n+1)) ⟨hs, hr⟩ _
  have hd := LinearMap.congr_fun (rawBoundary_squared (V := V)) (Finsupp.single s 1)
  have hh := H.contraction_apply n le_rfl _ hb
  rw [show rawBoundary (rawBoundary (Finsupp.single s 1)) = 0 from hd, map_zero, add_zero] at hh
  rw [map_add, hh, twice]

lemma newCycle_size (s : Finset V) (hs : s ∈ X.faces) (hr : s.card = n+1) :
    size (Finsupp.single s 1 + H.hom (rawBoundary (Finsupp.single s 1))) ≤ 1+R*(n+1) := by
  have hb : rawBoundary (Finsupp.single s 1) ∈ supported (graded X.faces n) := by
    apply boundary_graded X.faces (fun {_ _} hs h => X.downward hs h) n
    exact single_mem_supported (P := graded X.faces (n+1)) ⟨hs, hr⟩ _
  exact (size_add_le _ _).trans (Nat.add_le_add (size_single_le _ _)
    ((H.size_apply n le_rfl _ hb).trans
      (Nat.mul_le_mul_left R (by simpa [hr] using boundary_single_size s (1 : k)))))

noncomputable def extend (S : ℕ)
    (fill : ∀ c : Raw V, c ∈ supported (graded X.faces (n+1)) →
      rawBoundary c = 0 → size c ≤ 1+R*(n+1) →
      ∃ b : Raw V, b ∈ supported (graded X.faces (n+2)) ∧
        rawBoundary b = c ∧ size b ≤ S) : BoundedCone X (n+1) (max R S) := by
  classical
  let z (s : Finset V) := Finsupp.single s 1 + H.hom (rawBoundary (Finsupp.single s 1))
  have hex (s : Finset V) (hs : s ∈ X.faces ∧ s.card = n+1) :
      ∃ b : Raw V, b ∈ supported (graded X.faces (n+2)) ∧
        rawBoundary b = z s ∧ size b ≤ S :=
    fill (z s) (H.newCycle_supported s hs.1 hs.2)
      (H.newCycle_cycle s hs.1 hs.2) (H.newCycle_size s hs.1 hs.2)
  let f (s : Finset V) : Raw V :=
    if hs : s ∈ X.faces ∧ s.card = n+1 then (hex s hs).choose
    else H.hom (Finsupp.single s 1)
  let T : Raw V →ₗ[k] Raw V := Finsupp.linearCombination k f
  have hT (s : Finset V) : T (Finsupp.single s 1) = f s := by simp [T]
  have hold (s : Finset V) (hs : s.card ≤ n) :
      T (Finsupp.single s 1) = H.hom (Finsupp.single s 1) := by
    rw [hT]
    simp only [f, dite_eq_right (show ¬(s ∈ X.faces ∧ s.card = n+1) from by omega)]
  have hboundary (s : Finset V) (hs : s.card ≤ n+1) :
      T (rawBoundary (Finsupp.single s 1)) = H.hom (rawBoundary (Finsupp.single s 1)) := by
    rw [rawBoundary_single, map_sum, map_sum]
    apply Finset.sum_congr rfl
    intro v hv
    apply hold
    rw [Finset.card_erase_of_mem hv]
    omega
  refine ⟨T, ?_, ?_, ?_⟩
  · intro s hs hn
    by_cases he : s.card = n+1
    · rw [hT]
      have hspec := (hex s ⟨hs, he⟩).choose_spec.1
      dsimp only [f]
      rw [dite_eq_left (show s ∈ X.faces ∧ s.card = n+1 from ⟨hs, he⟩)]
      simpa only [he, Nat.add_assoc] using hspec
    · rw [hold s (by omega)]
      exact H.support s hs (by omega)
  · intro s hs hn
    rw [hboundary s hn]
    by_cases he : s.card = n+1
    · rw [hT]
      have hb : rawBoundary (f s) = z s := by
        dsimp only [f]
        rw [dite_eq_left (show s ∈ X.faces ∧ s.card = n+1 from ⟨hs, he⟩)]
        exact (hex s ⟨hs, he⟩).choose_spec.2.1
      rw [hb]
      dsimp [z]
      rw [add_assoc, twice, add_zero]
    · rw [hold s (by omega)]
      exact H.contraction s hs (by omega)
  · intro s hs hn
    by_cases he : s.card = n+1
    · rw [hT]
      have hb : size (f s) ≤ S := by
        dsimp only [f]
        rw [dite_eq_left (show s ∈ X.faces ∧ s.card = n+1 from ⟨hs, he⟩)]
        exact (hex s ⟨hs, he⟩).choose_spec.2.2
      exact hb.trans (Nat.le_max_right _ _)
    · rw [hold s (by omega)]
      exact (H.bound s hs (by omega)).trans (Nat.le_max_left _ _)

noncomputable def initial (X : CoboundaryExpanders.InfiniteChains.Complex V) (a : V) (ha : {a} ∈ X.faces) :
    BoundedCone X 0 1 where
  hom := rawCone a
  support := by
    intro s hs hn
    have he : s = ∅ := Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hn)
    subst s
    simpa [rawCone_single] using
      (single_mem_supported (P := graded X.faces 1) ⟨ha, by simp⟩ (1 : k))
  contraction := by
    intro s _ _
    exact LinearMap.congr_fun (raw_contraction a) (Finsupp.single s 1)
  bound := by
    intro s _ _
    exact (size_rawCone_le _ _).trans (size_single_le _ _)

end BoundedCone

def vertices (c : Raw V) : Finset V := c.support.biUnion id

lemma mem_vertices (c : Raw V) (s : Finset V) (hs : c s ≠ 0) (v : V) (hv : v ∈ s) :
    v ∈ vertices c := Finset.mem_biUnion.mpr ⟨s, Finsupp.mem_support_iff.mpr hs, hv⟩

lemma vertices_card_le (P : Set (Finset V)) (r : ℕ) (c : Raw V)
    (hc : c ∈ supported (graded P r)) : (vertices c).card ≤ r * size c := by
  calc
    (vertices c).card ≤ ∑ s ∈ c.support, s.card := Finset.card_biUnion_le
    _ = r * size c := by
      rw [Finset.sum_congr rfl (fun s hs =>
        ((mem_supported _ _).mp hc s (Finsupp.mem_support_iff.mp hs)).2)]
      simp [size, Nat.mul_comm]

def allowed (X : CoboundaryExpanders.InfiniteChains.Complex V) (bad : V → Prop) (A : Finset V) : CoboundaryExpanders.InfiniteChains.Complex V where
  faces := {s | s ∈ X.faces ∧ ∀ v ∈ s, bad v → v ∈ A}
  empty_mem := ⟨X.empty_mem, by simp⟩
  downward := fun hs hts => ⟨X.downward hs.1 hts, fun v hv => hs.2 v (hts hv)⟩

omit [DecidableEq V] in
lemma allowed_forget (X : CoboundaryExpanders.InfiniteChains.Complex V) (bad : V → Prop) (A : Finset V) (r : ℕ) :
    supported (graded (allowed X bad A).faces r) ≤ supported (graded X.faces r) :=
  supported_mono (fun _ hs => ⟨hs.1.1, hs.2⟩)

lemma removeBad (X : CoboundaryExpanders.InfiniteChains.Complex V) (bad : V → Prop) (r R : ℕ)
    (linkFill : ∀ v, bad v → ∀ c : Raw V,
      c ∈ supported (graded X.faces r) → rawBoundary c = 0 →
      ∃ b : Raw V,
        b ∈ supported (graded {s | s ∈ X.faces ∧
          (∀ w ∈ s, ¬bad w) ∧ insert v s ∈ X.faces} r) ∧
        rawBoundary b = link v c ∧ size b ≤ R * size c)
    (A : Finset V) (hA : ∀ v ∈ A, bad v) (c : Raw V)
    (hc : c ∈ supported (graded (allowed X bad A).faces r)) (hz : rawBoundary c = 0) :
    ∃ e c' : Raw V,
      e ∈ supported (graded X.faces (r+1)) ∧
      c' ∈ supported (graded (allowed X bad ∅).faces r) ∧
      rawBoundary c' = 0 ∧ rawBoundary e + c' = c ∧
      size e + size c' ≤ (2*R+2)^A.card * size c := by
  induction A using Finset.induction_on generalizing c with
  | empty =>
    refine ⟨0, c, Submodule.zero_mem _, hc, hz, by simp, ?_⟩
    simp
  | @insert v A hv ih =>
    have hcX := allowed_forget X bad (insert v A) r hc
    obtain ⟨b, hb, hdb, hsize⟩ := linkFill v (hA v (Finset.mem_insert_self _ _)) c hcX hz
    let P : Set (Finset V) := {s | s ∈ X.faces ∧ (∀ w ∈ s, ¬ bad w) ∧ insert v s ∈ X.faces}
    have hbP : b ∈ supported (graded P r) := hb
    have hbA : b ∈ supported (graded (allowed X bad A).faces r) := by
      apply supported_mono (P := graded P r) (Q := graded (allowed X bad A).faces r) ?_ hbP
      intro s hs
      exact ⟨⟨hs.1.1, fun w hw hbad => False.elim (hs.1.2.1 w hw hbad)⟩, hs.2⟩
    have hwA : without v c ∈ supported (graded (allowed X bad A).faces r) := by
      have hw := without_supported v (graded (allowed X bad (insert v A)).faces r) c hc
      apply supported_mono (P := {s | s ∈ graded (allowed X bad (insert v A)).faces r ∧ v ∉ s})
        (Q := graded (allowed X bad A).faces r) ?_ hw
      intro s hs
      refine ⟨⟨hs.1.1.1, ?_⟩, hs.1.2⟩
      intro w hw hbad
      rcases Finset.mem_insert.mp (hs.1.1.2 w hw hbad) with he | he
      · exact False.elim (hs.2 (he ▸ hw))
      · exact he
    have hz' := elimination_cycle v c b hz hdb
    obtain ⟨e, c', he, hc', hz'', hec', hbound⟩ :=
      ih (fun w hw => hA w (Finset.mem_insert_of_mem hw))
        (without v c + b) (Submodule.add_mem _ hwA hbA) hz'
    have hcone : rawCone v b ∈ supported (graded X.faces (r+1)) :=
      rawCone_graded v P X.faces r (fun s hs _ => hs.2.2) b hbP
    refine ⟨rawCone v b + e, c', Submodule.add_mem _ hcone he, hc', hz'', ?_, ?_⟩
    · rw [map_add, add_assoc, hec']
      exact elimination_identity v c b hdb
    · have hnew : size (without v c + b) ≤ (R+1)*size c := by
        have hw := without_size v c
        have hadd := size_add_le (without v c) b
        nlinarith
      have hconesize : size (rawCone v b) ≤ R*size c := (size_rawCone_le _ _).trans hsize
      have hp : 1 ≤ (2*R+2)^A.card := Nat.one_le_pow _ _ (by omega)
      have hh := Nat.mul_le_mul_left ((2*R+2)^A.card) hnew
      have hbnd := size_add_le (rawCone v b) e
      rw [Finset.card_insert_of_notMem hv, pow_succ]
      nlinarith

def relabel (f : V → W) : Raw V →ₗ[k] Raw W :=
  Finsupp.lmapDomain k k (Finset.image f)

omit [DecidableEq V] in
@[simp] lemma relabel_single (f : V → W) (s : Finset V) (a : k) :
    relabel f (Finsupp.single s a) = Finsupp.single (s.image f) a := by
  simp [relabel]

omit [DecidableEq V] in
lemma relabel_size (f : V → W) (c : Raw V) : size (relabel f c) ≤ size c := by
  have h := size_map_le (relabel f) Set.univ 1 (fun s _ => by
    rw [relabel_single]; exact size_single_le _ _) c (by rw [mem_supported]; simp)
  simpa using h

omit [DecidableEq V] in
lemma relabel_supported (f : V → W) (P : Set (Finset V)) (Q : Set (Finset W))
    (h : ∀ s ∈ P, s.image f ∈ Q) (c : Raw V) (hc : c ∈ supported P) :
    relabel f c ∈ supported Q := by
  apply map_supported _ P Q _ c hc
  intro s hs a
  rw [relabel_single]
  exact single_mem_supported (h s hs) a

omit [DecidableEq V] in
lemma relabel_graded (f : V → W) (P : Set (Finset V)) (Q : Set (Finset W)) (r : ℕ)
    (h : ∀ s ∈ P, s.image f ∈ Q)
    (hinj : ∀ s ∈ P, Set.InjOn f (s : Set V))
    (c : Raw V) (hc : c ∈ supported (graded P r)) :
    relabel f c ∈ supported (graded Q r) := by
  apply relabel_supported f (graded P r) (graded Q r) _ c hc
  intro s hs
  exact ⟨h s hs.1, (Finset.card_image_of_injOn (hinj s hs.1)).trans hs.2⟩

omit [DecidableEq V] in
lemma relabel_injective (f : V → W) (hf : Function.Injective f) :
    Function.Injective (relabel f) :=
  Finsupp.mapDomain_injective (Finset.image_injective hf)

lemma relabel_boundary (f : V → W) (hf : Function.Injective f) :
    rawBoundary.comp (relabel f) = (relabel f).comp rawBoundary := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext
  intro a
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, relabel_single,
    rawBoundary_single, map_sum, Finset.sum_image, hf.injOn]
  apply Finset.sum_congr rfl
  intro v hv
  rw [Finset.image_erase hf]

omit [DecidableEq V] in
lemma relabel_comp {U : Type} [DecidableEq U] (f : V → W) (g : W → U) :
    (relabel g).comp (relabel f) = relabel (g ∘ f) := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext
  intro a
  simp [Finset.image_image]

lemma relabel_id : relabel (id : V → V) = LinearMap.id := by
  apply Finsupp.lhom_ext'
  intro s
  apply LinearMap.ext
  intro a
  simp

lemma relabel_retraction (f : V → W) (g : W → V) (P : Set (Finset W))
    (h : ∀ s ∈ P, ∀ w ∈ s, f (g w) = w)
    (c : Raw W) (hc : c ∈ supported P) : relabel f (relabel g c) = c := by
  apply linear_eq_on_supported ((relabel f).comp (relabel g)) LinearMap.id P _ c hc
  intro s hs
  simp only [LinearMap.comp_apply, relabel_single, LinearMap.id_apply]
  congr 1
  rw [Finset.image_image]
  calc
    s.image (f ∘ g) = s.image id := Finset.image_congr (fun w hw => h s hs w hw)
    _ = s := Finset.image_id

end CoboundaryExpanders.InfiniteChains.Cone

open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix

namespace CoboundaryExpanders.InfiniteChains.Cone
open Attachment
variable {V W : Type} [DecidableEq V] [DecidableEq W]

def unlabel (f : V → W) (hf : Function.Injective f) : Raw W →ₗ[k] Raw V :=
  Finsupp.lmapDomain k k (fun s : Finset W => s.preimage f hf.injOn)

omit [DecidableEq V] [DecidableEq W] in
@[simp] lemma unlabel_single (f : V → W) (hf : Function.Injective f) (s : Finset W) (a : k) :
    unlabel f hf (Finsupp.single s a) = Finsupp.single (s.preimage f hf.injOn) a := by
  simp [unlabel]

omit [DecidableEq V] in
lemma preimage_image (f : V → W) (hf : Function.Injective f) (s : Finset V) :
    (s.image f).preimage f hf.injOn = s := by
  ext v
  simp [hf.eq_iff]

omit [DecidableEq V] in
@[simp] lemma unlabel_relabel (f : V → W) (hf : Function.Injective f) (c : Raw V) :
    unlabel f hf (relabel f c) = c := by
  have he : (unlabel f hf).comp (relabel f) = LinearMap.id := by
    apply Finsupp.lhom_ext'
    intro s
    apply LinearMap.ext
    intro a
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, relabel_single, unlabel_single,
      preimage_image f hf s, LinearMap.id_apply]
  exact LinearMap.congr_fun he c

omit [DecidableEq W] in
lemma unlabel_size (f : V → W) (hf : Function.Injective f) (c : Raw W) :
    size (unlabel f hf c) ≤ size c := by
  have h := size_map_le (unlabel f hf) Set.univ 1 (fun s _ => by
    rw [unlabel_single]; exact size_single_le _ _) c (by rw [mem_supported]; simp)
  simpa using h

structure FaceModel (X : CoboundaryExpanders.InfiniteChains.Complex V) (Y : CoboundaryExpanders.InfiniteChains.Complex W) where
  vertex : V → W
  injective : Function.Injective vertex
  face_iff : ∀ s : Finset V, s.image vertex ∈ Y.faces ↔ s ∈ X.faces
  cover : ∀ t ∈ Y.faces, ∃ s ∈ X.faces, s.image vertex = t

namespace FaceModel
variable {X : CoboundaryExpanders.InfiniteChains.Complex V} {Y : CoboundaryExpanders.InfiniteChains.Complex W} (M : FaceModel X Y)

omit [DecidableEq V] in
lemma relabel_supported (c : Raw V) (hc : c ∈ supported X.faces) :
    relabel M.vertex c ∈ supported Y.faces :=
  Cone.relabel_supported M.vertex X.faces Y.faces (fun s hs => (M.face_iff s).mpr hs) c hc

omit [DecidableEq V] in
lemma unlabel_face (t : Finset W) (ht : t ∈ Y.faces) :
    t.preimage M.vertex M.injective.injOn ∈ X.faces ∧
      (t.preimage M.vertex M.injective.injOn).image M.vertex = t ∧
        (t.preimage M.vertex M.injective.injOn).card = t.card := by
  obtain ⟨s,hs,he⟩ := M.cover t ht
  subst t
  rw [preimage_image M.vertex M.injective s]
  exact ⟨hs,rfl,(Finset.card_image_of_injective s M.injective).symm⟩

lemma unlabel_graded (r : ℕ) (c : Raw W) (hc : c ∈ supported (graded Y.faces r)) :
    unlabel M.vertex M.injective c ∈ supported (graded X.faces r) := by
  apply map_supported _ (graded Y.faces r) (graded X.faces r) _ c hc
  intro t ht a
  rw [unlabel_single]
  have hh := M.unlabel_face t ht.1
  exact single_mem_supported (P := graded X.faces r) ⟨hh.1,hh.2.2.trans ht.2⟩ a

omit [DecidableEq V] in
lemma relabel_unlabel (c : Raw W) (hc : c ∈ supported Y.faces) :
    relabel M.vertex (unlabel M.vertex M.injective c) = c := by
  apply linear_eq_on_supported ((relabel M.vertex).comp (unlabel M.vertex M.injective))
    LinearMap.id Y.faces _ c hc
  intro t ht
  simp only [LinearMap.comp_apply,unlabel_single,relabel_single,LinearMap.id_apply,
    (M.unlabel_face t ht).2.1]

lemma unlabel_boundary (c : Raw W) (hc : c ∈ supported Y.faces) :
    unlabel M.vertex M.injective (rawBoundary c) =
      rawBoundary (unlabel M.vertex M.injective c) := by
  apply linear_eq_on_supported ((unlabel M.vertex M.injective).comp rawBoundary)
    (rawBoundary.comp (unlabel M.vertex M.injective)) Y.faces _ c hc
  intro t ht
  obtain ⟨s,hs,he⟩ := M.cover t ht
  subst t
  rw [← relabel_single M.vertex s 1]
  change unlabel M.vertex M.injective (rawBoundary (relabel M.vertex (Finsupp.single s 1))) = _
  have hb := LinearMap.congr_fun (Cone.relabel_boundary M.vertex M.injective) (Finsupp.single s 1)
  change rawBoundary (relabel M.vertex (Finsupp.single s 1)) =
    relabel M.vertex (rawBoundary (Finsupp.single s 1)) at hb
  simp only [LinearMap.comp_apply] at *
  rw [hb,unlabel_relabel,unlabel_relabel]

def pullCone {n R : ℕ} (H : BoundedCone Y n R) : BoundedCone X n R where
  hom := (unlabel M.vertex M.injective).comp (H.hom.comp (relabel M.vertex))
  support := by
    intro s hs hn
    change unlabel M.vertex M.injective (H.hom (relabel M.vertex (Finsupp.single s 1))) ∈ _
    rw [relabel_single]
    have hc := Finset.card_image_of_injective s M.injective
    have hh := H.support (s.image M.vertex) ((M.face_iff s).mpr hs) (hc.trans_le hn)
    rw [hc] at hh
    exact M.unlabel_graded (s.card+1) _ hh
  contraction := by
    intro s hs hn
    have hc := Finset.card_image_of_injective s M.injective
    have hin := (M.face_iff s).mpr hs
    have hsupport := H.support (s.image M.vertex) hin (hc.trans_le hn)
    have hplain := supported_mono (P := graded Y.faces ((s.image M.vertex).card+1))
      (Q := Y.faces) (fun _ ht => ht.1) hsupport
    have hh := congrArg (unlabel M.vertex M.injective)
      (H.contraction (s.image M.vertex) hin (hc.trans_le hn))
    rw [map_add,M.unlabel_boundary _ hplain] at hh
    have hb := LinearMap.congr_fun (Cone.relabel_boundary M.vertex M.injective) (Finsupp.single s 1)
    change rawBoundary (relabel M.vertex (Finsupp.single s 1)) =
      relabel M.vertex (rawBoundary (Finsupp.single s 1)) at hb
    rw [relabel_single] at hb
    rw [hb,unlabel_single,preimage_image M.vertex M.injective s] at hh
    simpa only [LinearMap.comp_apply,relabel_single] using hh
  bound := by
    intro s hs hn
    change size (unlabel M.vertex M.injective (H.hom (relabel M.vertex (Finsupp.single s 1)))) ≤ _
    apply (unlabel_size _ _ _).trans
    rw [relabel_single]
    exact H.bound (s.image M.vertex) ((M.face_iff s).mpr hs)
      ((Finset.card_image_of_injective s M.injective).trans_le hn)

def pushCone {n R : ℕ} (H : BoundedCone X n R) : BoundedCone Y n R where
  hom := (relabel M.vertex).comp (H.hom.comp (unlabel M.vertex M.injective))
  support := by
    intro t ht hn
    obtain ⟨s,hs,he⟩ := M.cover t ht
    subst t
    rw [Finset.card_image_of_injective s M.injective] at hn ⊢
    change relabel M.vertex (H.hom (unlabel M.vertex M.injective (Finsupp.single (s.image M.vertex) 1))) ∈ _
    rw [unlabel_single,preimage_image M.vertex M.injective s]
    exact Cone.relabel_graded M.vertex X.faces Y.faces (s.card+1)
      (fun a ha => (M.face_iff a).mpr ha) (fun _ _ => M.injective.injOn)
      _ (H.support s hs hn)
  contraction := by
    intro t ht hn
    obtain ⟨s,hs,he⟩ := M.cover t ht
    subst t
    rw [Finset.card_image_of_injective s M.injective] at hn
    change rawBoundary (relabel M.vertex (H.hom (unlabel M.vertex M.injective (Finsupp.single (s.image M.vertex) 1)))) +
      relabel M.vertex (H.hom (unlabel M.vertex M.injective (rawBoundary (Finsupp.single (s.image M.vertex) 1)))) = _
    rw [←relabel_single,unlabel_relabel]
    have hb (c : Raw V) := LinearMap.congr_fun (Cone.relabel_boundary M.vertex M.injective) c
    change ∀ c : Raw V, rawBoundary (relabel M.vertex c) = relabel M.vertex (rawBoundary c) at hb
    rw [hb,hb,unlabel_relabel,←map_add,H.contraction s hs hn]
  bound := by
    intro t ht hn
    obtain ⟨s,hs,he⟩ := M.cover t ht
    subst t
    rw [Finset.card_image_of_injective s M.injective] at hn
    change size (relabel M.vertex (H.hom (unlabel M.vertex M.injective (Finsupp.single (s.image M.vertex) 1)))) ≤ _
    rw [unlabel_single,preimage_image M.vertex M.injective s]
    exact (relabel_size _ _).trans (H.bound s hs hn)

end FaceModel
end CoboundaryExpanders.InfiniteChains.Cone

end

section
open scoped BigOperators
open scoped BigOperators Matrix
open scoped Matrix
open scoped BigOperators InnerProductSpace

namespace CoboundaryExpanders.InfiniteChains.Cone
open Attachment
variable {V : Type} [DecidableEq V]
attribute [local instance] Classical.propDecidable

def VertexPath (X : CoboundaryExpanders.InfiniteChains.Complex V) (x y : V) : Prop :=
  Relation.ReflTransGen (fun a b => ({a,b}:Finset V) ∈ X.faces) x y

def vertexEval (P : V → Prop) : Raw V →ₗ[k] k :=
  Finsupp.linearCombination k (fun s => ∑v∈s, (if P v then 1 else 0 : k))
omit [DecidableEq V] in
@[simp] lemma vertexEval_single (P : V → Prop) (s : Finset V) (a : k) :
    vertexEval P (Finsupp.single s a) = a * ∑v∈s, (if P v then 1 else 0 : k) := by
  simp [vertexEval]

lemma vertexEval_boundary {X : CoboundaryExpanders.InfiniteChains.Complex V} (P : V → Prop)
    (hP : ∀ a b, ({a,b}:Finset V) ∈ X.faces → (P a ↔ P b))
    (c : Raw V) (hc : c ∈ supported (graded X.faces 2)) :
    vertexEval P (rawBoundary c) = 0 := by
  have hsingle (s : Finset V) (hs : s ∈ graded X.faces 2) :
      vertexEval P (rawBoundary (Finsupp.single s 1)) = 0 := by
    obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hs.2
    have hp := hP a b hs.1
    rw [rawBoundary_single,Finset.sum_insert (show a ∉ ({b}:Finset V) by simpa using hab),
      Finset.sum_singleton,map_add]
    have hea : ({a,b}:Finset V).erase a = {b} := by simp [hab]
    have heb : ({a,b}:Finset V).erase b = {a} := by
      rw [Finset.erase_insert_of_ne hab,Finset.erase_singleton]
      rfl
    rw [hea,heb,vertexEval_single,vertexEval_single]
    simp only [one_mul,Finset.sum_singleton]
    by_cases ha : P a
    · have hb := hp.mp ha
      simp only [ite_eq_left ha,ite_eq_left hb]
      exact CharTwo.add_self_eq_zero _
    · have hb : ¬P b := fun h => ha (hp.mpr h)
      simp only [ite_eq_right ha,ite_eq_right hb,zero_add]
  rw [←Finsupp.sum_single c,Finsupp.sum,map_sum,map_sum]
  apply Finset.sum_eq_zero
  intro s hs
  have he : Finsupp.single s (c s) = c s • Finsupp.single s (1:k) := by simp
  rw [he,map_smul,map_smul,hsingle s ((mem_supported _ c).mp hc s (Finsupp.mem_support_iff.mp hs)),smul_zero]

theorem BoundedCone.vertexPath {X : CoboundaryExpanders.InfiniteChains.Complex V} {n R : ℕ} (H : BoundedCone X n R)
    (hn : 1 ≤ n) (x y : V) (hx : ({x}:Finset V) ∈ X.faces)
    (hy : ({y}:Finset V) ∈ X.faces) : VertexPath X x y := by
  let P : V → Prop := VertexPath X x
  have hP (a b : V) (hab : ({a,b}:Finset V) ∈ X.faces) : P a ↔ P b := by
    constructor
    · intro ha; exact ha.tail hab
    · intro hb; exact hb.tail (by simpa [Finset.pair_comm] using hab)
  let c : Raw V := Finsupp.single {x} 1+Finsupp.single {y} 1
  have hc : c ∈ supported (graded X.faces 1) := by
    dsimp only [c]
    apply Submodule.add_mem
    · exact single_mem_supported (P:=graded X.faces 1) ⟨hx,Finset.card_singleton x⟩ _
    · exact single_mem_supported (P:=graded X.faces 1) ⟨hy,Finset.card_singleton y⟩ _
  have hz : rawBoundary c = 0 := by
    simp only [c,map_add,rawBoundary_single,Finset.sum_singleton,Finset.erase_singleton]
    exact twice _
  have hb := vertexEval_boundary P hP (H.hom c) (H.map_graded 1 hn c hc)
  rw [H.fills 1 hn c hc hz] at hb
  have hpx : P x := Relation.ReflTransGen.refl
  by_contra hpy
  have hpy' : ¬P y := hpy
  simp only [c,map_add,vertexEval_single,Finset.sum_singleton,one_mul,ite_eq_left hpx,ite_eq_right hpy',add_zero] at hb
  exact one_ne_zero hb
end CoboundaryExpanders.InfiniteChains.Cone

end

open scoped Polynomial BigOperators

namespace CoboundaryExpanders.InfiniteChains.Cone

section
open Attachment
variable {V W : Type} [DecidableEq V] [DecidableEq W]

lemma exactIn_equivalence (e : V ≃ W) (P : Set (Finset V)) (Q : Set (Finset W))
    (he : ∀ s, s ∈ P ↔ s.image e ∈ Q) (r : ℕ) (hQ : ExactIn Q r) : ExactIn P r := by
  intro c hc hz
  have hm (s : Finset W) (hs : s ∈ Q) : s.image e.symm ∈ P := by
    apply (he _).mpr
    simpa only [Finset.image_image,Equiv.apply_symm_apply,Function.comp_def,Finset.image_id'] using hs
  have ha : relabel e c ∈ supported (graded Q r) :=
    relabel_graded e P Q r (fun s hs => (he s).mp hs) (fun _ _ => e.injective.injOn) c hc
  have haz : rawBoundary (relabel e c) = 0 := by
    have h := LinearMap.congr_fun (relabel_boundary e e.injective) c
    change rawBoundary (relabel e c) = relabel e (rawBoundary c) at h
    rw [h,hz,map_zero]
  obtain ⟨b,hb,heq⟩ := hQ _ ha haz
  refine ⟨relabel e.symm b,relabel_graded e.symm Q P (r+1) hm
    (fun _ _ => e.symm.injective.injOn) b hb,?_⟩
  have h := LinearMap.congr_fun (relabel_boundary e.symm e.symm.injective) b
  change rawBoundary (relabel e.symm b) = relabel e.symm (rawBoundary b) at h
  rw [h,heq]
  exact relabel_retraction e.symm e (graded P r)
    (fun _ _ _ _ => e.symm_apply_apply _) c hc

lemma image_erase_of_injOn (f : V → W) (s : Finset V)
    (hf : Set.InjOn f (s : Set V)) (v : V) (hv : v ∈ s) :
    (s.erase v).image f = (s.image f).erase (f v) := by
  ext w
  constructor
  · rintro hw
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hw
    refine Finset.mem_erase.mpr ⟨?_,Finset.mem_image.mpr ⟨u,(Finset.mem_erase.mp hu).2,rfl⟩⟩
    intro he
    exact (Finset.mem_erase.mp hu).1 (hf (Finset.mem_erase.mp hu).2 hv he)
  · intro hw
    exact Finset.erase_image_subset_image_erase f s v hw
lemma relabel_boundary_on (f : V → W) (P : Set (Finset V))
    (hf : ∀ s ∈ P, Set.InjOn f (s : Set V))
    (c : Raw V) (hc : c ∈ supported P) :
    rawBoundary (relabel f c) = relabel f (rawBoundary c) := by
  apply linear_eq_on_supported (rawBoundary.comp (relabel f)) ((relabel f).comp rawBoundary) P _ c hc
  intro s hs
  simp only [LinearMap.comp_apply,relabel_single,rawBoundary_single,map_sum]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro v hv
    rw [image_erase_of_injOn f s (hf s hs) v hv]
  · exact hf s hs

theorem exactIn_retract (f : V → W) (g : W → V) (P : Set (Finset V)) (Q : Set (Finset W))
    (hf : ∀ s ∈ P, s.image f ∈ Q) (hg : ∀ s ∈ Q, s.image g ∈ P)
    (hfi : ∀ s ∈ P, Set.InjOn f (s : Set V))
    (hgi : ∀ s ∈ Q, Set.InjOn g (s : Set W))
    (hret : ∀ s ∈ P, ∀ v ∈ s, g (f v) = v)
    (r : ℕ) (hQ : ExactIn Q r) : ExactIn P r := by
  intro c hc hz
  have hfc := relabel_graded f P Q r hf hfi c hc
  have hfz : rawBoundary (relabel f c) = 0 := by
    rw [relabel_boundary_on f (graded P r) (fun s hs => hfi s hs.1) c hc,hz,map_zero]
  obtain ⟨b,hb,hbc⟩ := hQ _ hfc hfz
  refine ⟨relabel g b,relabel_graded g Q P (r+1) hg hgi b hb,?_⟩
  rw [relabel_boundary_on g (graded Q (r+1)) (fun s hs => hgi s hs.1) b hb,hbc]
  exact relabel_retraction g f (graded P r) (fun s hs => hret s hs.1) c hc
noncomputable def BoundedCone.retract {X : CoboundaryExpanders.InfiniteChains.Complex V} {Y : CoboundaryExpanders.InfiniteChains.Complex W} {n R : ℕ}
    (H : BoundedCone Y n R) (f : V → W) (g : W → V)
    (hf : ∀ s ∈ X.faces, s.image f ∈ Y.faces)
    (hg : ∀ s ∈ Y.faces, s.image g ∈ X.faces)
    (hfi : ∀ s ∈ X.faces, Set.InjOn f (s : Set V))
    (hgi : ∀ s ∈ Y.faces, Set.InjOn g (s : Set W))
    (hret : ∀ s ∈ X.faces, ∀ v ∈ s, g (f v) = v) : BoundedCone X n R where
  hom := (relabel g).comp (H.hom.comp (relabel f))
  support := by
    intro s hs hn
    have hcard : (s.image f).card = s.card := Finset.card_image_of_injOn (hfi s hs)
    have hH := H.support (s.image f) (hf s hs) (hcard.trans_le hn)
    simpa only [LinearMap.comp_apply,relabel_single,hcard] using
      relabel_graded g Y.faces X.faces ((s.image f).card+1) hg hgi _ hH
  contraction := by
    intro s hs hn
    have hcard : (s.image f).card = s.card := Finset.card_image_of_injOn (hfi s hs)
    have hH := H.support (s.image f) (hf s hs) (hcard.trans_le hn)
    have hb := relabel_boundary_on g (graded Y.faces ((s.image f).card+1))
      (fun t ht => hgi t ht.1) _ hH
    have hc := congrArg (relabel g) (H.contraction (s.image f) (hf s hs) (hcard.trans_le hn))
    have hbf := relabel_boundary_on f X.faces hfi (Finsupp.single s 1) (single_mem_supported hs 1)
    simp only [LinearMap.comp_apply,relabel_single] at hbf ⊢
    rw [hb,← hbf,← map_add,hc]
    simpa only [relabel_single] using relabel_retraction g f X.faces hret _ (single_mem_supported hs 1)
  bound := by
    intro s hs hn
    simp only [LinearMap.comp_apply,relabel_single]
    apply (relabel_size g _).trans
    exact H.bound (s.image f) (hf s hs) ((Finset.card_image_of_injOn (hfi s hs)).trans_le hn)

theorem relativeExactIn_retract (f : V → W) (g : W → V)
    (P Q : Set (Finset V)) (U T : Set (Finset W))
    (hQ : ∀ {s t}, s ∈ Q → t ⊆ s → t ∈ Q)
    (hf : ∀ s ∈ Q, s.image f ∈ T) (hg : ∀ s ∈ T, s.image g ∈ Q)
    (hfOld : ∀ s ∈ P ∩ Q, s.image f ∈ U) (hgOld : ∀ s ∈ U, s.image g ∈ P)
    (hfi : ∀ s ∈ Q, Set.InjOn f (s : Set V))
    (hgi : ∀ s ∈ T, Set.InjOn g (s : Set W)) (hUT : U ⊆ T)
    (hret : ∀ s ∈ Q, ∀ v ∈ s, g (f v) = v)
    (r : ℕ) (H : RelativeExactIn U T r) : RelativeExactIn P Q r := by
  intro c hc hz
  have hbc := boundary_supported Q hQ c (graded_forget Q r hc)
  have hz' : rawBoundary c ∈ supported (P ∩ Q) := by
    rw [mem_supported] at hz hbc ⊢
    exact fun s hs => ⟨hz s hs,hbc s hs⟩
  have hfc := relabel_graded f Q T r hf hfi c hc
  have hfz : rawBoundary (relabel f c) ∈ supported U := by
    rw [relabel_boundary_on f (graded Q r) (fun s hs => hfi s hs.1) c hc]
    exact relabel_supported f (P ∩ Q) U hfOld _ hz'
  obtain ⟨b,hb,hres⟩ := H _ hfc hfz
  refine ⟨relabel g b,relabel_graded g T Q (r+1) hg hgi b hb,?_⟩
  have hh := relabel_graded g U P r hgOld (fun s hs => hgi s (hUT hs)) _ hres
  rw [map_sub,← relabel_boundary_on g (graded T (r+1)) (fun s hs => hgi s hs.1) b hb,
    relabel_retraction g f (graded Q r) (fun s hs => hret s hs.1) c hc] at hh
  exact hh
end

section
variable {V : Type} [DecidableEq V]
def tagBy (F : Finset V) (v : V) : V ⊕ V := if v ∈ F then Sum.inl v else Sum.inr v
lemma untag_tagBy (F : Finset V) (v : V) : Sum.elim id id (tagBy F v) = v := by
  simp only [tagBy]; split <;> rfl
lemma tagBy_injective (F : Finset V) : Function.Injective (tagBy F) := by
  intro v w he
  have hh := congrArg (Sum.elim id id) he
  simpa only [untag_tagBy] using hh
lemma tagBy_left (F s : Finset V) : (s.image (tagBy F)).toLeft = s ∩ F := by
  ext v
  simp only [Finset.mem_toLeft,Finset.mem_image,Finset.mem_inter]
  constructor
  · rintro ⟨w,hw,he⟩
    by_cases hh : w ∈ F
    · simp only [tagBy,ite_eq_left hh,Sum.inl.injEq] at he
      exact he ▸ ⟨hw,hh⟩
    · simp [tagBy,hh] at he
  · rintro ⟨hv,hF⟩
    exact ⟨v,hv,by simp [tagBy,hF]⟩
lemma tagBy_right (F s : Finset V) : (s.image (tagBy F)).toRight = s \ F := by
  ext v
  simp only [Finset.mem_toRight,Finset.mem_image,Finset.mem_sdiff]
  constructor
  · rintro ⟨w,hw,he⟩
    by_cases hh : w ∈ F
    · simp [tagBy,hh] at he
    · simp only [tagBy,ite_eq_right hh,Sum.inr.injEq] at he
      exact he ▸ ⟨hw,hh⟩
  · rintro ⟨hv,hF⟩
    exact ⟨v,hv,by simp [tagBy,hF]⟩
lemma untag_image (s : Finset (V ⊕ V)) : s.image (Sum.elim id id) = s.toLeft ∪ s.toRight := by
  ext v
  simp only [Finset.mem_image,Finset.mem_union,Finset.mem_toLeft,Finset.mem_toRight]
  constructor
  · rintro ⟨(w|w),hw,he⟩
    · exact Or.inl (he ▸ hw)
    · exact Or.inr (he ▸ hw)
  · rintro (h|h)
    · exact ⟨Sum.inl v,h,rfl⟩
    · exact ⟨Sum.inr v,h,rfl⟩
end

open Attachment
variable {V W : Type} [DecidableEq V] [DecidableEq W] [Nonempty V]
lemma exactIn_of_image (f : V → W) (hinj : Function.Injective f)
    (P : Set (Finset V)) (Q : Set (Finset W))
    (hf : ∀ s ∈ P, s.image f ∈ Q)
    (hg : ∀ s ∈ Q, ∃ t ∈ P, t.image f = s)
    (r : ℕ) (H : ExactIn Q r) : ExactIn P r := by
  classical
  let g := Function.invFun f
  have hgf (v : V) : g (f v) = v := Function.leftInverse_invFun hinj v
  have hfg (s) (hs : s ∈ Q) (w) (hw : w ∈ s) : f (g w) = w := by
    obtain ⟨t,_,rfl⟩ := hg s hs
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hw
    rw [hgf]
  apply exactIn_retract f g P Q hf ?_ (fun _ _ => hinj.injOn) ?_ (fun _ _ v _ => hgf v) r H
  · intro s hs
    obtain ⟨t,ht,rfl⟩ := hg s hs
    simpa [Finset.image_image,Function.comp_def,hgf] using ht
  · intro s hs v hv w hw he
    rw [← hfg s hs v hv,← hfg s hs w hw,he]
end CoboundaryExpanders.InfiniteChains.Cone

end

end OAI
