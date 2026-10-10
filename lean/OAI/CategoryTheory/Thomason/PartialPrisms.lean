import Mathlib
import OAI.CategoryTheory.Thomason.PartialTables

namespace OAI

/-! Partial Prisms. -/

noncomputable section
universe u v w z


namespace Thomason.PartialNormalized
open DirectedComplex DirectedComplex.Table NormalizedChains OmegaCategory
variable {D : Type u} [PartialOrder D] {n N : ℕ}

lemma cutAtom_boundary (f : PartialHom (complex (Fin (N+1))) (complex D) n)
    (F : OmegaCategory.Functor (Oriental N) (truncation n (complex D).nu).val)
    (hf : ∀ x, f.image x = F.map x) (hn : 0<n) (θ : Fin (N+1) →o Fin 2)
    (a : Fin (N+1)) (l : List (Fin (N+1))) (ha : (a::l).Pairwise (· < ·))
    (hl : l.length = n+1) :
    (cutHom f hn θ).image (simplexAtom a l (ha.imp le_of_lt)).table =
      (cutHom f hn θ).image (truncate n true (simplexAtom a l (ha.imp le_of_lt)).table) := by
  cases l using List.reverseRecOn with
  | nil => simp at hl
  | append_singleton l b =>
    let A := simplexAtom a (l++[b]) (ha.imp le_of_lt)
    have hpw : ((a::l)++[b]).Pairwise (· ≤ ·) := ha.imp le_of_lt
    by_cases hθ : θ b = 0
    · have hz : ∀ z ∈ a::(l++[b]), θ z = 0 := by
        intro z hz
        have hz' : z ∈ (a::l)++[b] := hz
        have hzb : z ≤ b := by
          rcases List.mem_append.mp hz' with hz' | hz'
          · exact (List.pairwise_append.mp hpw).2.2 z hz' b (by simp)
          · have he : z=b := by simpa using hz'
            exact he.le
        have he := θ.monotone hzb
        rw [hθ] at he
        exact le_antisymm he (Fin.zero_le _)
      have hs : ∀ p e, (A.table.row p e).val ∈ supportedOn {z | θ z = 0} :=
        fun p e => supportedOn_mono hz (A.supported p e)
      calc
        _ = f.image A.table := cutHom_image_of_supported f hn θ A.table hs
        _ = F.map A.table := hf _
        _ = F.map (truncate n true A.table) :=
          ((truncation n (complex D).nu).val.target_eq_self_of_source_eq_self
            ((truncation n (complex D).nu).property _)).symm.trans (F.map_target n A.table).symm
        _ = f.image (truncate n true A.table) := (hf _).symm
        _ = _ := (cutHom_image_of_supported f hn θ _ (truncate_supported A.table hs n true)).symm
    · apply PartialHom.image_boundary_of_oneStep
      · exact hl ▸ A.dimension
      · intro e
        have ht : A.table.row (n+1) e =
            (⟨bracket (a::(l++[b])), by
              simpa only [List.length_cons,hl] using (bracket_mem_grade (a::(l++[b])))⟩ : (complex (Fin (N+1))).Chain (n+1)) := by
          apply Subtype.ext
          have h := A.top e
          have he : (a::(l++[b])).length-1 = n+1 := by
            rw [List.length_cons,hl]; omega
          rw [he] at h
          exact h
        change (cutHom f hn θ).map n ((complex (Fin (N+1))).d n (A.table.row (n+1) e)) = _
        rw [ht]
        apply Subtype.ext
        change cutTotal f θ (boundary (bracket (a::(l++[b])))) =
          boundary (cutTotal f θ (bracket (a::(l++[b]))))
        rw [boundary_bracket (ha.imp le_of_lt),cutTotal_wordBoundary f θ _ (ha.imp le_of_lt),
          cutTotal_bracket f θ _ (ha.imp le_of_lt)]
        exact (cutWord_boundary_append_one f hn θ (a::l) b hpw
          (by simp only [List.length_append,List.length_singleton] at hl
              simp only [List.length_cons]; omega) hθ).symm

def finiteCut (f : PartialHom (complex (Fin (N+1))) (complex D) n)
    (F : OmegaCategory.Functor (Oriental N) (truncation n (complex D).nu).val)
    (hf : ∀ x, f.image x = F.map x) (hn : 0<n) (θ : Fin (N+1) →o Fin 2) :
    OmegaCategory.Functor (Oriental N) (truncation n (complex D).nu).val :=
  (cutHom f hn θ).extendOriental (cutAtom_boundary f F hf hn θ)

end Thomason.PartialNormalized

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.PartialHom
open Table
variable {K : DirectedComplex.{u}} {L : DirectedComplex.{v}} {M : DirectedComplex.{w}} {n : ℕ}

@[ext] theorem ext {f g : PartialHom K L n} (h : ∀ p, f.map p = g.map p) : f = g := by
  have hm : f.map = g.map := funext h
  cases f
  cases g
  cases hm
  rfl

def precomp (f : PartialHom L M n) (a : Hom K L) : PartialHom K M n where
  map p := (f.map p).comp (a.map p)
  map_d p hp x := by
    change f.map p (a.map p (K.d p x)) = _
    rw [a.map_d,f.map_d p hp]
    rfl
  map_augmentation x := (f.map_augmentation _).trans (a.map_augmentation x)
  map_positive p x hx := f.map_positive p _ (a.map_positive p x hx)

lemma precomp_table (f : PartialHom L M n) (a : Hom K L) (x : Table K) :
    (f.precomp a).table x = f.table (a.table x) := by
  ext p b
  simp only [table,precomp]
  split_ifs <;> rfl

lemma precomp_image (f : PartialHom L M n) (a : Hom K L) (x : Table K) :
    (f.precomp a).image x = f.image (a.table x) :=
  congrArg (OmegaCategory.truncationUnit n M.nu).map (f.precomp_table a x)

end Thomason.DirectedComplex.PartialHom

end

noncomputable section
universe u v w z


namespace Thomason.PartialNormalized
open DirectedComplex NormalizedChains
variable {E : Type u} [PartialOrder E] {D : Type v} [PartialOrder D]
variable {B : Type w} [PartialOrder B] {n : ℕ}

lemma homTotal_precomp (a : B →o E) (f : PartialHom (complex E) (complex D) n)
    (c : Chains B) : homTotal (f.precomp (complexMap a)) c = homTotal f (map a c) := by
  classical
  rw [chains_eq_sum_bracket c]
  simp only [Finsupp.sum,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro w _
  congr 1
  obtain ⟨l,hl⟩ := w
  cases l with
  | nil => rw [homTotal_bracket,map_bracket a (by simp),homTotal_bracket]; rfl
  | cons b l =>
    have h := homTotal_map f l.length ((complexMap a).map l.length
      ⟨bracket (b::l),bracket_mem_grade _⟩)
    exact (homTotal_map (f.precomp (complexMap a)) l.length
      ⟨bracket (b::l),bracket_mem_grade _⟩).trans h.symm

lemma homVertex_precomp (a : B →o E) (f : PartialHom (complex E) (complex D) n) (b : B) :
    homVertex (f.precomp (complexMap a)) b = homVertex f (a b) := by
  apply bracket_singleton_injective
  change bracket [homVertex (f.precomp (complexMap a)) b] = bracket [homVertex f (a b)]
  rw [← homTotal_vertex,homTotal_precomp,map_bracket a (by simp)]
  exact homTotal_vertex f (a b)

lemma cutWord_precomp (a : B →o E) (f : PartialHom (complex E) (complex D) n)
    (θ : E →o Fin 2) (l : List B) (hl : l.Pairwise (· ≤ ·)) :
    cutWord (f.precomp (complexMap a)) (θ.comp a) l = cutWord f θ (l.map a) := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l b ih =>
    rw [List.map_append,List.map_singleton,cutWord_append,cutWord_append]
    change (if θ (a b) = 0 then _ else _) = (if θ (a b) = 0 then _ else _)
    split
    · rw [homTotal_precomp,map_bracket a hl,List.map_append,List.map_singleton]
    · rw [homVertex_precomp,ih (List.pairwise_append.mp hl).1]

lemma cutTotal_precomp (a : B →o E) (f : PartialHom (complex E) (complex D) n)
    (θ : E →o Fin 2) (c : Chains B) :
    cutTotal (f.precomp (complexMap a)) (θ.comp a) c = cutTotal f θ (map a c) := by
  classical
  rw [chains_eq_sum_bracket c]
  simp only [Finsupp.sum,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro w _
  congr 1
  rw [cutTotal_bracket _ _ w.val (w.property.imp le_of_lt),
    map_bracket a (w.property.imp le_of_lt),
    cutTotal_bracket _ _ (w.val.map a)
      (List.pairwise_map.mpr (w.property.imp (fun h => a.monotone h.le)))]
  exact cutWord_precomp a f θ w.val (w.property.imp le_of_lt)

lemma cutHom_precomp (a : B →o E) (f : PartialHom (complex E) (complex D) n)
    (hn : 0<n) (θ : E →o Fin 2) :
    cutHom (f.precomp (complexMap a)) hn (θ.comp a) = (cutHom f hn θ).precomp (complexMap a) := by
  apply PartialHom.ext
  intro p
  apply AddMonoidHom.ext
  intro x
  exact Subtype.ext (cutTotal_precomp a _ θ x.val)

end Thomason.PartialNormalized

end

noncomputable section
universe u v w z


namespace Thomason
open DirectedComplex DirectedComplex.Table NormalizedChains OmegaCategory
variable {K : DirectedComplex.{u}} {n M N : ℕ}

lemma simplexInverse_natural (a : Fin (M+1) →o Fin (N+1)) (p : ℕ)
    (x : (complex (Fin (M+1))).Chain p) :
    atomCounitInverse p ((complexMap a).map p x) =
      (complexMap a).nu.lambdaMap p (atomCounitInverse p x) := by
  apply oriental_lambdaCounit_injective p
  rw [counit_atomInverse]
  have hh := lambdaNu_left_inv (Hom.comp (complex (Fin (M+1))).lambdaCounit (complexMap a))
  rw [lambdaNuForward_counit] at hh
  have h := congrArg (fun H => H.map p (atomCounitInverse p x)) hh
  change (complex (Fin (N+1))).lambdaCounitMap p
    ((complexMap a).nu.lambdaMap p (atomCounitInverse p x)) =
      (complexMap a).map p ((complex (Fin (M+1))).lambdaCounitMap p (atomCounitInverse p x)) at h
  rw [counit_atomInverse] at h
  exact h.symm

lemma liftedPartial_natural_below (a : Fin (M+1) →o Fin (N+1))
    (F : OmegaCategory.Functor (Oriental N) (truncation n K.nu).val)
    (p : ℕ) (hp : p<n) :
    (liftedPartial (OmegaCategory.Functor.comp (complexMap a).nu F)).map p =
      ((liftedPartial F).precomp (complexMap a)).map p := by
  apply AddMonoidHom.ext
  intro x
  change K.lambdaCounitMap p (liftedChainMap (OmegaCategory.Functor.comp (complexMap a).nu F) p x) =
    K.lambdaCounitMap p (liftedChainMap F p ((complexMap a).map p x))
  congr 1
  apply truncationUnit_lambdaMap_injective K.nu n p hp
  rw [liftedChainMap_unit,liftedChainMap_unit]
  exact (LinearMap.congr_fun (OmegaCategory.Functor.lambdaMap_comp (complexMap a).nu F p) _).trans
    (congrArg (F.lambdaMap p) (simplexInverse_natural a p x).symm)

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.PartialNormalized
open DirectedComplex DirectedComplex.Table NormalizedChains OmegaCategory
variable {E : Type u} [PartialOrder E] {D : Type v} [PartialOrder D] {n : ℕ}

lemma homWord_congr_low (f g : PartialHom (complex E) (complex D) n)
    (hfg : ∀ p, p<n → f.map p = g.map p) (l : List E) (hl : l.length ≤ n) :
    homWord f l = homWord g l := by
  cases l with
  | nil => rfl
  | cons a l =>
    change (f.map l.length _).val = (g.map l.length _).val
    rw [hfg l.length (by simp only [List.length_cons] at hl; omega)]

lemma homTotal_congr_low (f g : PartialHom (complex E) (complex D) n)
    (hfg : ∀ p, p<n → f.map p = g.map p) {k : ℕ} (hk : k≤n)
    (c : Chains E) (hc : c ∈ grade k) : homTotal f c = homTotal g c := by
  classical
  rw [chains_eq_sum_bracket c]
  simp only [Finsupp.sum,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro w hw
  congr 1
  rw [homTotal_bracket,homTotal_bracket]
  exact homWord_congr_low f g hfg _ (by
    have he := (mem_grade_iff k c).mp hc w (Finsupp.mem_support_iff.mp hw)
    omega)

lemma homVertex_congr_low (f g : PartialHom (complex E) (complex D) n)
    (hfg : ∀ p, p<n → f.map p = g.map p) (hn : 0<n) (a : E) :
    homVertex f a = homVertex g a := by
  apply bracket_singleton_injective
  change bracket [homVertex f a] = bracket [homVertex g a]
  rw [← homTotal_vertex,← homTotal_vertex]
  exact homTotal_congr_low f g hfg (by change 1 ≤ n; omega) _ (bracket_mem_grade [a])

lemma cutWord_congr_low (f g : PartialHom (complex E) (complex D) n)
    (hfg : ∀ p, p<n → f.map p = g.map p) (hn : 0<n)
    (θ : E →o Fin 2) (l : List E) (hl : l.length ≤ n) :
    cutWord f θ l = cutWord g θ l := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l a ih =>
    rw [cutWord_append,cutWord_append]
    split
    · exact homTotal_congr_low f g hfg hl _ (bracket_mem_grade _)
    · rw [homVertex_congr_low f g hfg hn a,
        ih (by simp only [List.length_append,List.length_singleton] at hl; omega)]

lemma cutTotal_congr_low (f g : PartialHom (complex E) (complex D) n)
    (hfg : ∀ p, p<n → f.map p = g.map p) (hn : 0<n)
    (θ : E →o Fin 2) {k : ℕ} (hk : k≤n) (c : Chains E) (hc : c ∈ grade k) :
    cutTotal f θ c = cutTotal g θ c := by
  classical
  rw [chains_eq_sum_bracket c]
  simp only [Finsupp.sum,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro w hw
  congr 1
  rw [cutTotal_bracket _ _ _ (w.property.imp le_of_lt),cutTotal_bracket _ _ _ (w.property.imp le_of_lt)]
  exact cutWord_congr_low f g hfg hn θ _ (by
    have he := (mem_grade_iff k c).mp hc w (Finsupp.mem_support_iff.mp hw)
    omega)

lemma cutWord_congr_append_one (f g : PartialHom (complex E) (complex D) n)
    (hfg : ∀ p, p<n → f.map p = g.map p) (hn : 0<n)
    (θ : E →o Fin 2) (l : List E) (a : E) (hl : l.length ≤ n) (ha : θ a ≠ 0) :
    cutWord f θ (l++[a]) = cutWord g θ (l++[a]) := by
  rw [cutWord_append,cutWord_append,ite_eq_right ha,ite_eq_right ha,
    homVertex_congr_low f g hfg hn a,cutWord_congr_low f g hfg hn θ l hl]

lemma cutTable_atom_congr (f g : PartialHom (complex E) (complex D) n)
    (hfg : ∀ p, p<n → f.map p = g.map p) (hn : 0<n)
    (θ : E →o Fin 2) (a : E) (l : List E) (ha : (a::l).Pairwise (· < ·))
    (hl : l.length ≤ n) (r : List E) (b : E) (he : a::l = r++[b]) (hb : θ b ≠ 0) :
    (cutHom f hn θ).table (simplexAtom a l (ha.imp le_of_lt)).table =
      (cutHom g hn θ).table (simplexAtom a l (ha.imp le_of_lt)).table := by
  let A := simplexAtom a l (ha.imp le_of_lt)
  ext p e
  simp only [PartialHom.table]
  split_ifs with hpn hpe
  · apply Subtype.ext
    exact cutTotal_congr_low f g hfg hn θ (by omega) _ (A.table.row p e).property
  · subst p
    by_cases hln : l.length < n
    · rw [row_above_fixed A.table A.dimension hln false,map_zero,map_zero]
    · have hlen : l.length = n := by omega
      have ht : (A.table.row n false).val = bracket (a::l) := by
        have ht := A.top false
        have he : (a::l).length-1 = n := by rw [List.length_cons,hlen]; omega
        rw [he] at ht
        exact ht
      apply Subtype.ext
      change cutTotal f θ (A.table.row n false).val = cutTotal g θ (A.table.row n false).val
      rw [ht,cutTotal_bracket _ _ _ (ha.imp le_of_lt),cutTotal_bracket _ _ _ (ha.imp le_of_lt),he]
      apply cutWord_congr_append_one f g hfg hn θ r b _ hb
      have h := congrArg List.length he
      simp only [List.length_cons,List.length_append] at h
      omega
  · rfl

end Thomason.PartialNormalized

end

noncomputable section
universe u v w z


namespace Thomason.PartialNormalized
open DirectedComplex DirectedComplex.Table NormalizedChains OmegaCategory
variable {D : Type u} [PartialOrder D] {n N : ℕ}

lemma finiteCut_congr
    (f g : PartialHom (complex (Fin (N+1))) (complex D) n)
    (F : OmegaCategory.Functor (Oriental N) (truncation n (complex D).nu).val)
    (hf : ∀ x, f.image x = F.map x) (hg : ∀ x, g.image x = F.map x)
    (hfg : ∀ p, p<n → f.map p = g.map p) (hn : 0<n) (θ : Fin (N+1) →o Fin 2) :
    finiteCut f F hf hn θ = finiteCut g F hg hn θ := by
  apply oriental_functor_ext_truncated (truncation n (complex D).nu).property
  intro a l ha hl
  change (cutHom f hn θ).image (simplexAtom a l (ha.imp le_of_lt)).table =
    (cutHom g hn θ).image (simplexAtom a l (ha.imp le_of_lt)).table
  have hlast : ∃ r b, a::l = r++[b] := by
    cases l using List.reverseRecOn with
    | nil => exact ⟨[],a,rfl⟩
    | append_singleton r b => exact ⟨a::r,b,rfl⟩
  obtain ⟨r,b,he⟩ := hlast
  by_cases hb : θ b = 0
  · have hpw : (r++[b]).Pairwise (· ≤ ·) := he ▸ ha.imp le_of_lt
    have hz : ∀ z ∈ a::l, θ z = 0 := by
      intro z hz
      rw [he] at hz
      have hzb : z ≤ b := by
        rcases List.mem_append.mp hz with hz | hz
        · exact (List.pairwise_append.mp hpw).2.2 z hz b (by simp)
        · have he' : z=b := by simpa using hz
          exact he'.le
      have h := θ.monotone hzb
      rw [hb] at h
      exact le_antisymm h (Fin.zero_le _)
    have hs : ∀ p e, ((simplexAtom a l (ha.imp le_of_lt)).table.row p e).val ∈
        supportedOn {z | θ z = 0} := fun p e =>
      supportedOn_mono hz ((simplexAtom a l (ha.imp le_of_lt)).supported p e)
    rw [cutHom_image_of_supported f hn θ _ hs,cutHom_image_of_supported g hn θ _ hs,hf,hg]
  · exact congrArg (truncationUnit n (complex D).nu).map
      (cutTable_atom_congr f g hfg hn θ a l ha hl r b he hb)

end Thomason.PartialNormalized

end

noncomputable section
universe u v w z


namespace Thomason
open DirectedComplex NormalizedChains OmegaCategory PartialNormalized
variable {P : Type u} [PartialOrder P] {n : ℕ}

def finiteTableCut (hn : 0<n) {N : ℕ}
    (F : OmegaCategory.Functor (Oriental N) (truncation n (complex P).nu).val)
    (θ : Fin (N+1) →o Fin 2) :
    OmegaCategory.Functor (Oriental N) (truncation n (complex P).nu).val :=
  finiteCut (liftedPartial F) F (liftedPartial_image F) hn θ

lemma finiteTableCut_natural (hn : 0<n) {M N : ℕ}
    (a : Fin (M+1) →o Fin (N+1))
    (F : OmegaCategory.Functor (Oriental N) (truncation n (complex P).nu).val)
    (θ : Fin (N+1) →o Fin 2) :
    finiteTableCut hn (OmegaCategory.Functor.comp (complexMap a).nu F) (θ.comp a) =
      OmegaCategory.Functor.comp (complexMap a).nu (finiteTableCut hn F θ) := by
  let g := (liftedPartial F).precomp (complexMap a)
  have hg : ∀ x, g.image x = (OmegaCategory.Functor.comp (complexMap a).nu F).map x := by
    intro x
    exact ((liftedPartial F).precomp_image (complexMap a) x).trans (liftedPartial_image F _)
  calc
    _ = finiteCut g (OmegaCategory.Functor.comp (complexMap a).nu F) hg hn (θ.comp a) :=
      finiteCut_congr _ g _ (liftedPartial_image _) hg
        (liftedPartial_natural_below a F) hn (θ.comp a)
    _ = _ := by
      apply OmegaCategory.Functor.ext
      funext x
      change (PartialNormalized.cutHom ((liftedPartial F).precomp (complexMap a)) hn (θ.comp a)).image x = _
      erw [PartialNormalized.cutHom_precomp,PartialHom.precomp_image]
      rfl

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.DirectedComplex.PartialHom
open Table OmegaCategory
variable {K : DirectedComplex.{u}} {L : DirectedComplex.{v}} {n : ℕ}

def ofHom (f : Hom K L) (n : ℕ) : PartialHom K L n where
  map := f.map
  map_d p _ x := f.map_d p x
  map_augmentation := f.map_augmentation
  map_positive := f.map_positive

lemma ofHom_table (f : Hom K L) (x : Table K) :
    (ofHom f n).table x = truncate n false (f.table x) := by
  ext p b
  simp only [table,ofHom,truncate_row,Hom.table]

lemma ofHom_image (f : Hom K L) (x : Table K) :
    (ofHom f n).image x = (truncationUnit n L.nu).map (f.table x) := by
  change (truncationUnit n L.nu).map ((ofHom f n).table x) = _
  rw [ofHom_table]
  exact ((truncationUnit n L.nu).map_source n (f.table x)).trans
    ((truncation n L.nu).property _)

end Thomason.DirectedComplex.PartialHom

end

noncomputable section
universe u v w z


namespace Thomason.PartialNormalized
open DirectedComplex NormalizedChains
variable {E : Type u} [PartialOrder E] {D : Type v} [PartialOrder D] {n : ℕ}

lemma cutWord_const_one (f : PartialHom (complex E) (complex D) n) (l : List E) :
    cutWord f (OrderHom.const E (1 : Fin 2)) l = bracket (l.map (homVertex f)) := by
  induction l using List.reverseRecOn with
  | nil => simp
  | append_singleton l a ih =>
    rw [cutWord_append,ite_eq_right (by change (1 : Fin 2) ≠ 0; decide),ih,append_bracket,
      List.map_append,List.map_singleton]

lemma cutTotal_const_zero (f : PartialHom (complex E) (complex D) n) (c : Chains E) :
    cutTotal f (OrderHom.const E (0 : Fin 2)) c = homTotal f c := by
  apply cutTotal_eq_homTotal_of_supported
  apply (mem_supportedOn_iff _ c).mpr
  simp

lemma cutTotal_const_one (f : PartialHom (complex E) (complex D) n) (hn : 0<n) (c : Chains E) :
    cutTotal f (OrderHom.const E (1 : Fin 2)) c = map (homVertexOrderHom f hn) c := by
  classical
  rw [chains_eq_sum_bracket c]
  simp only [Finsupp.sum,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro w _
  congr 1
  rw [cutTotal_bracket _ _ w.val (w.property.imp le_of_lt),cutWord_const_one,
    map_bracket (homVertexOrderHom f hn) (w.property.imp le_of_lt)]
  rfl

lemma cutHom_const_zero (f : PartialHom (complex E) (complex D) n) (hn : 0<n) :
    cutHom f hn (OrderHom.const E (0 : Fin 2)) = f := by
  apply PartialHom.ext
  intro p
  apply AddMonoidHom.ext
  intro c
  apply Subtype.ext
  exact (cutTotal_const_zero f c.val).trans (homTotal_map f p c)

lemma cutHom_const_one (f : PartialHom (complex E) (complex D) n) (hn : 0<n) :
    cutHom f hn (OrderHom.const E (1 : Fin 2)) =
      PartialHom.ofHom (complexMap (homVertexOrderHom f hn)) n := by
  apply PartialHom.ext
  intro p
  apply AddMonoidHom.ext
  intro c
  exact Subtype.ext (cutTotal_const_one f hn c.val)

lemma homVertex_ofHom (a : E →o D) (b : E) :
    homVertex (PartialHom.ofHom (complexMap a) n) b = a b := by
  apply bracket_singleton_injective
  change bracket [homVertex (PartialHom.ofHom (complexMap a) n) b] = bracket [a b]
  rw [← homTotal_vertex,homTotal_map (PartialHom.ofHom (complexMap a) n) 0
    ⟨bracket [b],bracket_mem_grade [b]⟩]
  change map a (bracket [b]) = bracket [a b]
  rw [map_bracket a (by simp)]
  rfl

end Thomason.PartialNormalized

end

noncomputable section
universe u v w z


namespace Thomason
open DirectedComplex NormalizedChains OmegaCategory
variable {K : DirectedComplex.{u}} {n N : ℕ}

lemma liftedPartial_of_nu_below (f : Hom (complex (Fin (N+1))) K) (p : ℕ) (hp : p<n) :
    (liftedPartial (OmegaCategory.Functor.comp f.nu (truncationUnit n K.nu))).map p = f.map p := by
  apply AddMonoidHom.ext
  intro x
  have he : liftedChainMap (OmegaCategory.Functor.comp f.nu (truncationUnit n K.nu)) p x =
      f.nu.lambdaMap p (atomCounitInverse p x) := by
    apply truncationUnit_lambdaMap_injective K.nu n p hp
    erw [liftedChainMap_unit,OmegaCategory.Functor.lambdaMap_comp]
    rfl
  change K.lambdaCounitMap p (liftedChainMap
    (OmegaCategory.Functor.comp f.nu (truncationUnit n K.nu)) p x) = _
  rw [he]
  change (orientalChain N f.nu).map p x = f.map p x
  rw [orientalChain_of_nu]

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason
open CategoryTheory Opposite Simplicial MonoidalCategory DirectedComplex NormalizedChains OmegaCategory

noncomputable def finiteTableNerveVertexMap (n : ℕ) (hn : 0<n) (P : Type u) [PartialOrder P] :
    streetNerve (truncation n (complex P).nu).val ⟶ nerve P where
  app m := ↾fun F => (PartialNormalized.homVertexOrderHom (liftedPartial F) hn).monotone.functor
  naturality m k a := by
    apply ConcreteCategory.hom_ext
    intro F
    apply nerve.ext_of_isThin
    funext i
    change PartialNormalized.homVertex
        (liftedPartial (OmegaCategory.Functor.comp (complexMap a.unop.toOrderHom).nu F)) i =
      PartialNormalized.homVertex (liftedPartial F) (a.unop.toOrderHom i)
    rw [PartialNormalized.homVertex_congr_low _ _ (liftedPartial_natural_below a.unop.toOrderHom F) hn]
    exact PartialNormalized.homVertex_precomp a.unop.toOrderHom (liftedPartial F) i

noncomputable def finitePosetTableNerveMap (n : ℕ) (P : Type u) [PartialOrder P] :
    nerve P ⟶ streetNerve (truncation n (complex P).nu).val :=
  posetTableNerveMap P ≫ streetNerveMap (truncationUnit n (complex P).nu)

lemma finitePosetTableNerveMap_vertex (n : ℕ) (hn : 0<n) (P : Type u) [PartialOrder P] :
    finitePosetTableNerveMap n P ≫ finiteTableNerveVertexMap n hn P = 𝟙 (nerve P) := by
  apply NatTrans.ext
  funext m
  apply ConcreteCategory.hom_ext
  intro s
  apply nerve.ext_of_isThin
  funext i
  change PartialNormalized.homVertex (liftedPartial (OmegaCategory.Functor.comp
    (complexMap (posetSimplexOrder s)).nu (truncationUnit n (complex P).nu))) i = s.obj i
  rw [PartialNormalized.homVertex_congr_low _ (PartialHom.ofHom (complexMap (posetSimplexOrder s)) n)
    (liftedPartial_of_nu_below (complexMap (posetSimplexOrder s))) hn,
    PartialNormalized.homVertex_ofHom]
  rfl

lemma finiteTableCut_const_zero {n N : ℕ} (hn : 0<n) (P : Type u) [PartialOrder P]
    (F : OmegaCategory.Functor (Oriental N) (truncation n (complex P).nu).val) :
    finiteTableCut hn F (OrderHom.const _ (0 : Fin 2)) = F := by
  apply OmegaCategory.Functor.ext
  funext x
  change (PartialNormalized.cutHom (liftedPartial F) hn (OrderHom.const _ (0 : Fin 2))).image x = _
  rw [PartialNormalized.cutHom_const_zero]
  exact liftedPartial_image F x

lemma finiteTableCut_const_one {n N : ℕ} (hn : 0<n) (P : Type u) [PartialOrder P]
    (F : OmegaCategory.Functor (Oriental N) (truncation n (complex P).nu).val) :
    finiteTableCut hn F (OrderHom.const _ (1 : Fin 2)) =
      OmegaCategory.Functor.comp
        (complexMap (PartialNormalized.homVertexOrderHom (liftedPartial F) hn)).nu
        (truncationUnit n (complex P).nu) := by
  apply OmegaCategory.Functor.ext
  funext x
  change (PartialNormalized.cutHom (liftedPartial F) hn (OrderHom.const _ (1 : Fin 2))).image x = _
  erw [PartialNormalized.cutHom_const_one,PartialHom.ofHom_image]
  rfl

noncomputable def finiteTableNerveCutCylinder (n : ℕ) (hn : 0<n) (P : Type u) [PartialOrder P] :
    streetNerve (truncation n (complex P).nu).val ⊗ Δ[1] ⟶
      streetNerve (truncation n (complex P).nu).val where
  app m := ↾fun z => finiteTableCut hn z.1 (SSet.stdSimplex.objEquiv z.2).toOrderHom
  naturality m k a := by
    apply ConcreteCategory.hom_ext
    intro z
    exact finiteTableCut_natural hn a.unop.toOrderHom z.1 (SSet.stdSimplex.objEquiv z.2).toOrderHom

noncomputable def finiteTableNerveCutHomotopy (n : ℕ) (hn : 0<n) (P : Type u) [PartialOrder P] :
    SSet.Homotopy (𝟙 (streetNerve (truncation n (complex P).nu).val))
      (finiteTableNerveVertexMap n hn P ≫ finitePosetTableNerveMap n P) where
  h := finiteTableNerveCutCylinder n hn P
  h₀ := by
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro F
    exact finiteTableCut_const_zero hn P F
  h₁ := by
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    intro F
    exact finiteTableCut_const_one hn P F
  rel := by
    apply NatTrans.ext
    funext m
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨x,hx⟩,θ⟩
    exact False.elim hx

lemma finiteTableNerveVertexMap_weakEquivalence (n : ℕ) (hn : 0<n) (P : Type u) [PartialOrder P] :
    simplicialWeakEquivalences (finiteTableNerveVertexMap n hn P) :=
  simplicialWeakEquivalence_of_simplicial_retract _ (finitePosetTableNerveMap n P)
    (finitePosetTableNerveMap_vertex n hn P) (finiteTableNerveCutHomotopy n hn P)

lemma finitePosetTableNerveMap_weakEquivalence (n : ℕ) (hn : 0<n) (P : Type u) [PartialOrder P] :
    simplicialWeakEquivalences (finitePosetTableNerveMap n P) := by
  apply simplicialWeakEquivalences.of_postcomp _ (finiteTableNerveVertexMap n hn P)
    (finiteTableNerveVertexMap_weakEquivalence n hn P)
  rw [finitePosetTableNerveMap_vertex]
  exact simplicialWeakEquivalences.id_mem _

lemma posetCategorificationFiniteUnit_tableMap (n : ℕ) (P : Type u) [PartialOrder P] :
    (categorificationFiniteAdjunction n).unit.app (nerve P) ≫
      streetNerveMap ((truncationFunctor n).map (posetCategorificationTableMap P)) =
        finitePosetTableNerveMap n P := by
  change (categorificationAdjunction.unit.app (nerve P) ≫
    streetNerveMap (truncationUnit n (categorification.obj (nerve P)))) ≫ _ = _
  erw [Category.assoc]
  have he : streetNerveMap (truncationUnit n (categorification.obj (nerve P))) ≫
      streetNerveMap ((truncationFunctor n).map (posetCategorificationTableMap P)) =
      streetNerveMap (posetCategorificationTableMap P) ≫ streetNerveMap (truncationUnit n (complex P).nu) := rfl
  erw [he,← Category.assoc,posetCategorificationUnit_tableMap]
  rfl

theorem posetCategorificationFiniteUnit_weakEquivalence (n : ℕ) (hn : 1 ≤ n)
    (P : Type u) [PartialOrder P] :
    simplicialWeakEquivalences
      ((categorificationFiniteAdjunction n).unit.app (CategoryTheory.nerve P)) := by
  have : IsIso (streetNerveMap ((truncationFunctor n).map (posetCategorificationTableMap P))) := by
    change IsIso ((streetNerveFinite n).map ((truncationFunctor n).map (posetCategorificationTableMap P)))
    infer_instance
  apply simplicialWeakEquivalences.of_postcomp _
    (streetNerveMap ((truncationFunctor n).map (posetCategorificationTableMap P)))
    (simplicialWeakEquivalences.of_isIso _)
  erw [posetCategorificationFiniteUnit_tableMap]
  exact finitePosetTableNerveMap_weakEquivalence n hn P

end Thomason

end

noncomputable section
universe u v w z


namespace Thomason.OmegaCategory
open CategoryTheory Limits
variable (C : Type u) [Category.{u} C]
def categorySkeletonObject (x : C) : (ofCategory C).OneSkeleton :=
  ⟨Arrow.mk (𝟙 x), rfl⟩
lemma categorySkeletonObject_left (x : (ofCategory C).OneSkeleton) :
    categorySkeletonObject C x.val.left = x := by
  apply Subtype.ext
  exact x.property

def categoryToSkeleton : C ⥤ (ofCategory C).OneSkeleton where
  obj := categorySkeletonObject C
  map f := ⟨Arrow.mk f, rfl, rfl, rfl⟩
  map_id _ := rfl
  map_comp {source middle target} f g := by
    apply Subtype.ext
    change Arrow.mk (f ≫ g) = Arrow.mk (f ≫ 𝟙 middle ≫ g)
    simp

lemma categorySkeleton_hom_left {x y : (ofCategory C).OneSkeleton} (f : x ⟶ y) :
    f.val.left = x.val.left := by
  have h : Arrow.mk (𝟙 f.val.left) = x.val := f.property.2.1
  have hh := congrArg (fun z : Arrow C => z.left) h
  exact hh
lemma categorySkeleton_hom_right {x y : (ofCategory C).OneSkeleton} (f : x ⟶ y) :
    f.val.right = y.val.left := by
  have h : Arrow.mk (𝟙 f.val.right) = y.val := f.property.2.2
  have hh := congrArg (fun z : Arrow C => z.left) h
  exact hh

def skeletonToCategory : (ofCategory C).OneSkeleton ⥤ C where
  obj x := x.val.left
  map f := eqToHom (categorySkeleton_hom_left C f).symm ≫ f.val.hom ≫
    eqToHom (categorySkeleton_hom_right C f)
  map_id x := by
    obtain ⟨a, rfl⟩ : ∃ a, categorySkeletonObject C a = x :=
      ⟨x.val.left, categorySkeletonObject_left C x⟩
    change 𝟙 a ≫ 𝟙 a ≫ 𝟙 a = 𝟙 a
    simp
  map_comp {x y z} f g := by
    simp only [one_comp_val]
    change eqToHom _ ≫ (f.val.hom ≫ eqToHom _ ≫ g.val.hom) ≫ eqToHom _ =
      (eqToHom _ ≫ f.val.hom ≫ eqToHom _) ≫
        (eqToHom _ ≫ g.val.hom ≫ eqToHom _)
    simp

lemma categoryToSkeleton_comp : categoryToSkeleton C ⋙ skeletonToCategory C = 𝟭 C := by
  refine CategoryTheory.Functor.ext (F := categoryToSkeleton C ⋙ skeletonToCategory C)
    (G := 𝟭 C) (fun _ => rfl) ?_
  intro x y f
  simp [categoryToSkeleton, skeletonToCategory]

lemma skeletonToCategory_comp : skeletonToCategory C ⋙ categoryToSkeleton C =
    𝟭 (ofCategory C).OneSkeleton := by
  refine CategoryTheory.Functor.ext (categorySkeletonObject_left C) ?_
  intro x y f
  apply Subtype.ext
  erw [one_eqToHom_comp_val, one_comp_eqToHom_val]
  change Arrow.mk (eqToHom _ ≫ f.val.hom ≫ eqToHom _) = f.val
  rcases f with ⟨⟨a,b,g⟩, hf⟩
  have ha : a = x.val.left := congrArg Arrow.left hf.2.1
  have hb : b = y.val.left := congrArg Arrow.left hf.2.2
  subst a; subst b
  change Arrow.mk (𝟙 _ ≫ g ≫ 𝟙 _) = Arrow.mk g
  simp

def categorySkeletonIso : Cat.of C ≅ Cat.of (ofCategory C).OneSkeleton where
  hom := (categoryToSkeleton C).toCatHom
  inv := (skeletonToCategory C).toCatHom
  hom_inv_id := by apply Cat.Hom.ext; exact categoryToSkeleton_comp C
  inv_hom_id := by apply Cat.Hom.ext; exact skeletonToCategory_comp C

instance : oneSkeletonCatFunctor.{u}.EssSurj where
  mem_essImage C := ⟨⟨ofCategory C, ofCategory_truncated C⟩, ⟨(categorySkeletonIso C).symm⟩⟩
instance : oneSkeletonCatFunctor.{u}.IsEquivalence where

end Thomason.OmegaCategory

end

noncomputable section
universe u v w z
open CategoryTheory Limits Opposite Simplicial MonoidalCategory

namespace Thomason.OneCat
abbrev Interval := ULift.{u} (Fin 2)
def endpoint (C : Cat.{u,u}) (b : Fin 2) : C ⟶ Cat.of (Interval.{u} × C) :=
  (Prod.sectR (ULift.up b) C).toCatHom
abbrev cylinder : Cat.{u,u} ⥤ Cat.{u,u} := tensorLeft (Cat.of Interval.{u})
def projection (C : Cat.{u,u}) : cylinder.obj C ⟶ C := (CategoryTheory.Prod.snd Interval C).toCatHom
@[reassoc] lemma endpoint_natural {C D : Cat.{u,u}} (f : C ⟶ D) (b : Fin 2) :
    endpoint C b ≫ cylinder.map f = f ≫ endpoint D b := rfl
@[reassoc] lemma projection_natural {C D : Cat.{u,u}} (f : C ⟶ D) :
    cylinder.map f ≫ projection D = projection C ≫ f := rfl
@[simp, reassoc] lemma endpoint_projection (C : Cat.{u,u}) (b : Fin 2) :
    endpoint C b ≫ projection C = 𝟙 C := rfl

lemma pushout_deformation {A E X Y : Cat.{u,u}} {a : A ⟶ X} {i : A ⟶ E}
    {j : X ⟶ Y} {v : E ⟶ Y} (sq : IsPushout a i j v)
    (r : E ⟶ A) (ri : i ≫ r = 𝟙 A)
    (H : cylinder.obj E ⟶ E)
    (h₀ : endpoint E 0 ≫ H = r ≫ i)
    (h₁ : endpoint E 1 ≫ H = 𝟙 E)
    (hA : cylinder.map i ≫ H = projection A ≫ i) :
    ∃ (p : Y ⟶ X) (H' : cylinder.obj Y ⟶ Y),
      j ≫ p = 𝟙 X ∧ endpoint Y 0 ≫ H' = p ≫ j ∧
      endpoint Y 1 ≫ H' = 𝟙 Y := by
  let p : Y ⟶ X := sq.desc (𝟙 X) (r ≫ a) (by simp [← Category.assoc,ri])
  have pj : j ≫ p = 𝟙 X := sq.inl_desc _ _ _
  have pv : v ≫ p = r ≫ a := sq.inr_desc _ _ _
  have sw := sq.map cylinder
  have hw : cylinder.map a ≫ (projection X ≫ j) = cylinder.map i ≫ (H ≫ v) := by
    rw [projection_natural_assoc, ← Category.assoc (cylinder.map i),hA]
    simpa only [Category.assoc] using congrArg (projection A ≫ ·) sq.w
  let Q : cylinder.obj Y ⟶ Y := sw.desc (projection X ≫ j) (H ≫ v) hw
  have Qj : cylinder.map j ≫ Q = projection X ≫ j := sw.inl_desc _ _ _
  have Qv : cylinder.map v ≫ Q = H ≫ v := sw.inr_desc _ _ _
  refine ⟨p,Q,pj,?_,?_⟩
  · apply sq.hom_ext
    · erw [← Category.assoc, ← endpoint_natural, Category.assoc, Qj, ← Category.assoc, endpoint_projection,
        Category.id_comp, ← Category.assoc, pj, Category.id_comp]
    · erw [← Category.assoc, ← endpoint_natural, Category.assoc, Qv, ← Category.assoc, h₀,
        ← Category.assoc v p j, pv]
      simpa only [Category.assoc] using congrArg (r ≫ ·) sq.w.symm
  · apply sq.hom_ext
    · erw [Category.comp_id, ← Category.assoc, ← endpoint_natural, Category.assoc, Qj,
        ← Category.assoc, endpoint_projection, Category.id_comp]
    · erw [Category.comp_id, ← Category.assoc, ← endpoint_natural, Category.assoc, Qv,
        ← Category.assoc, h₁, Category.id_comp]
end Thomason.OneCat

end

end OAI
