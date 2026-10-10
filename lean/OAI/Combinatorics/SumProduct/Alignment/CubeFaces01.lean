import Mathlib
import OAI.Geometry.NilpotentCharts.Coordinates
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
section
section
noncomputable section
end
end
 

 
section
open scoped commutatorElement Pointwise
namespace CubeFaces
variable {G ι : Type*} [Group G] [DecidableEq ι]
 
def face (D : Finset ι) : G →* (Finset ι → G) where
  toFun g v := if D ⊆ v then g else 1
  map_one' := by funext v; simp
  map_mul' g h := by funext v; dsimp; split_ifs <;> simp

@[simp] lemma face_apply (D v : Finset ι) (g : G) :
    face D g v = if D ⊆ v then g else 1 := rfl

lemma face_commutator (D E : Finset ι) (g h : G) :
    ⁅face D g, face E h⁆ = face (D ∪ E) ⁅g,h⁆ := by
  funext v
  simp only [commutatorElement_def, Pi.mul_apply, Pi.inv_apply, face_apply,
    Finset.union_subset_iff]
  by_cases hD : D ⊆ v <;> by_cases hE : E ⊆ v <;> simp [hD, hE]

 
def cube (H : Filtration G) (I : Finset ι) (k : ℕ) : Subgroup (Finset ι → G) :=
  ⨆ D : Finset ι, ⨆ (_ : D ⊆ I), (H.level (D.card + k)).map (face D)

lemma face_mem_cube (H : Filtration G) {I D : Finset ι} {k : ℕ}
    (hD : D ⊆ I) {g : G} (hg : g ∈ H.level (D.card + k)) :
    face D g ∈ cube H I k := by
  have hle : (H.level (D.card + k)).map (face D) ≤ cube H I k :=
    le_iSup_of_le D (le_iSup_of_le hD le_rfl)
  exact hle ⟨g, hg, rfl⟩

 
def upper (a : ι) : (Finset ι → G) →* (Finset ι → G) where
  toFun f v := if a ∈ v then f v else 1
  map_one' := by funext v; simp
  map_mul' f g := by funext v; dsimp; split_ifs <;> simp

lemma upper_face (a : ι) (D : Finset ι) :
    (upper a).comp (face D : G →* (Finset ι → G)) = face (insert a D) := by
  ext g v
  by_cases ha : a ∈ v <;> by_cases hD : D ⊆ v <;>
    simp [upper, face, Finset.insert_subset_iff, ha, hD]

lemma map_upper_cube (H : Filtration G) (a : ι) (I : Finset ι) (k : ℕ) :
    (cube H I (k + 1)).map (upper a) =
      ⨆ E : Finset ι, ⨆ (_ : E ⊆ I),
        (H.level (E.card + k + 1)).map (face (insert a E)) := by
  simp only [cube, Subgroup.map_iSup, Subgroup.map_map, upper_face, Nat.add_assoc]

@[simp] lemma upper_face_apply (a : ι) (D : Finset ι) (g : G) :
    upper a (face D g) = face (insert a D) g :=
  DFunLike.congr_fun (upper_face a D) g

lemma face_upper_commutator_mem (H : Filtration G) (a : ι)
    {I D E : Finset ι} {k : ℕ} (hD : D ⊆ I) (hE : E ⊆ I)
    {g h : G} (hg : g ∈ H.level (D.card + k))
    (hh : h ∈ H.level (E.card + (k + 1))) :
    ⁅face D g, upper a (face E h)⁆ ∈ (cube H I (k + 1)).map (upper a) := by
  rw [upper_face_apply, face_commutator, Finset.union_insert]
  have hdeg : (D ∪ E).card + (k + 1) ≤ (D.card + k) + (E.card + (k + 1)) := by
    have := Finset.card_union_le D E
    omega
  have hc : ⁅g,h⁆ ∈ H.level ((D ∪ E).card + (k + 1)) :=
    H.antitone hdeg (H.commutator_le _ _ (Subgroup.commutator_mem_commutator hg hh))
  exact ⟨face (D ∪ E) ⁅g,h⁆, face_mem_cube H (Finset.union_subset hD hE) hc,
    upper_face_apply a (D ∪ E) ⁅g,h⁆⟩

lemma cube_le_normalizer_upper (H : Filtration G) (a : ι) (I : Finset ι) (k : ℕ) :
    cube H I k ≤ Subgroup.normalizer ((cube H I (k + 1)).map (upper a)) := by
  let R := (cube H I (k + 1)).map (upper a)
  change (⨆ D : Finset ι, ⨆ (_ : D ⊆ I),
    (H.level (D.card + k)).map (face D)) ≤ Subgroup.normalizer R
  refine iSup_le fun D => iSup_le fun hD => ?_
  rintro f ⟨g, hg, rfl⟩
  have hc (g : G) (hg : g ∈ H.level (D.card + k)) :
      ∀ z ∈ R, face D g * z * (face D g)⁻¹ ∈ R := by
    have hle : cube H I (k + 1) ≤
        R.comap ((MulAut.conj (face D g)).toMonoidHom.comp (upper a)) := by
      refine iSup_le fun E => iSup_le fun hE => ?_
      rintro f ⟨h, hh, rfl⟩
      change face D g * upper a (face E h) * (face D g)⁻¹ ∈ R
      have hm : upper a (face E h) ∈ R :=
        ⟨face E h, face_mem_cube H hE hh, rfl⟩
      have hcomm := face_upper_commutator_mem H a hD hE hg hh
      have heq : face D g * upper a (face E h) * (face D g)⁻¹ =
          ⁅face D g, upper a (face E h)⁆ * upper a (face E h) := by
        simp [commutatorElement_def, mul_assoc]
      rw [heq]
      exact R.mul_mem hcomm hm
    rintro z ⟨u, hu, rfl⟩
    exact hle hu
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · exact hc g hg z
  · intro hz
    have ht := hc g⁻¹ ((H.level _).inv_mem hg) _ hz
    simpa [map_inv, mul_assoc] using ht

lemma cube_insert_le (H : Filtration G) (a : ι) (I : Finset ι) (k : ℕ) :
    cube H (insert a I) k ≤ cube H I k ⊔ (cube H I (k + 1)).map (upper a) := by
  refine iSup_le fun D => iSup_le fun hD => ?_
  rintro f ⟨g, hg, rfl⟩
  by_cases haD : a ∈ D
  · have hE : D.erase a ⊆ I := by
      intro x hx
      rcases Finset.mem_erase.mp hx with ⟨hxa, hx⟩
      exact (Finset.mem_insert.mp (hD hx)).resolve_left hxa
    have hcard := Finset.card_erase_add_one haD
    have hg' : g ∈ H.level ((D.erase a).card + (k + 1)) := by
      have he : (D.erase a).card + (k + 1) = D.card + k := by omega
      rwa [he]
    apply Subgroup.mem_sup_right
    refine ⟨face (D.erase a) g, face_mem_cube H hE hg', ?_⟩
    rw [upper_face_apply, Finset.insert_erase haD]
  · have hDI : D ⊆ I := by
      intro x hx
      rcases Finset.mem_insert.mp (hD hx) with hxa | hxi
      · exact False.elim (haD (hxa ▸ hx))
      · exact hxi
    exact Subgroup.mem_sup_left (face_mem_cube H hDI hg)

 

lemma cube_decompose (H : Filtration G) (a : ι) (I : Finset ι) (k : ℕ)
    {f : Finset ι → G} (hf : f ∈ cube H (insert a I) k) :
    ∃ l ∈ cube H I k, ∃ u ∈ cube H I (k + 1), f = l * upper a u := by
  have hx := cube_insert_le H a I k hf
  change f ∈ (↑(cube H I k ⊔ (cube H I (k + 1)).map (upper a)) : Set _) at hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (cube_le_normalizer_upper H a I k)] at hx
  rcases hx with ⟨l, hl, z, ⟨u, hu, rfl⟩, hmul⟩
  exact ⟨l, hl, u, hu, hmul.symm⟩

 
def evaluation (v : Finset ι) : (Finset ι → G) →* G where
  toFun f := f v
  map_one' := rfl
  map_mul' _ _ := rfl

lemma cube_insert_irrelevant (H : Filtration G) {I : Finset ι} {a : ι}
    (ha : a ∉ I) {k : ℕ} {f : Finset ι → G} (hf : f ∈ cube H I k)
    (v : Finset ι) : f (insert a v) = f v := by
  have hle : cube H I k ≤ (evaluation (insert a v)).eqLocus (evaluation v) := by
    refine iSup_le fun D => iSup_le fun hD => ?_
    rintro f ⟨g, hg, rfl⟩
    change face D g (insert a v) = face D g v
    have he : D ⊆ insert a v ↔ D ⊆ v := by
      constructor
      · intro hd x hx
        have hxa : x ≠ a := by rintro rfl; exact ha (hD hx)
        exact (Finset.mem_insert.mp (hd hx)).resolve_left hxa
      · intro hd
        exact hd.trans (Finset.subset_insert a v)
    simp only [face_apply, he]
  exact hle hf

lemma cube_eval_mem (H : Filtration G) {I : Finset ι} {k : ℕ}
    {f : Finset ι → G} (hf : f ∈ cube H I k) (v : Finset ι) : f v ∈ H.level k := by
  have hle : cube H I k ≤ (H.level k).comap (evaluation v) := by
    refine iSup_le fun D => iSup_le fun hD => ?_
    rintro f ⟨g, hg, rfl⟩
    change face D g v ∈ H.level k
    simp only [face_apply]
    split_ifs
    · exact H.antitone (Nat.le_add_left k D.card) hg
    · exact (H.level k).one_mem
  exact hle hf

lemma cube_shift_le (H : Filtration G) (I : Finset ι) {i j : ℕ} (h : i ≤ j) :
    cube H I j ≤ cube H I i := by
  refine iSup_le fun D => iSup_le fun hD => ?_
  exact (Subgroup.map_mono (H.antitone (Nat.add_le_add_left h _))).trans
    (le_iSup_of_le D (le_iSup_of_le hD le_rfl))

lemma cube_restrict (H : Filtration G) {I : Finset ι} {k : ℕ}
    {f : Finset ι → G} (hf : f ∈ cube H I k) (v : Finset ι) :
    f (v ∩ I) = f v := by
  have hle : cube H I k ≤ (evaluation (v ∩ I)).eqLocus (evaluation v) := by
    refine iSup_le fun D => iSup_le fun hD => ?_
    rintro f ⟨g,hg,rfl⟩
    change face D g (v ∩ I) = face D g v
    simp only [face_apply, Finset.subset_inter_iff, hD, and_true]
  exact hle hf

lemma cube_normalizes (H : Filtration G) (I : Finset ι) (k : ℕ) :
    cube H I 0 ≤ Subgroup.normalizer (cube H I k) := by
  refine iSup_le fun D => iSup_le fun hD => ?_
  rintro f ⟨g,hg,rfl⟩
  have hc (g : G) (hg : g ∈ H.level (D.card + 0)) :
      ∀ z ∈ cube H I k, face D g * z * (face D g)⁻¹ ∈ cube H I k := by
    have hle : cube H I k ≤ (cube H I k).comap (MulAut.conj (face D g)).toMonoidHom := by
      refine iSup_le fun E => iSup_le fun hE => ?_
      rintro f ⟨h,hh,rfl⟩
      change face D g * face E h * (face D g)⁻¹ ∈ cube H I k
      have hdeg : (D ∪ E).card + k ≤ (D.card + 0) + (E.card + k) := by
        have := Finset.card_union_le D E
        omega
      have hcomm : ⁅face D g, face E h⁆ ∈ cube H I k := by
        rw [face_commutator]
        exact face_mem_cube H (Finset.union_subset hD hE)
          (H.antitone hdeg (H.commutator_le _ _ (Subgroup.commutator_mem_commutator hg hh)))
      have heq : face D g * face E h * (face D g)⁻¹ = ⁅face D g, face E h⁆ * face E h := by
        simp [commutatorElement_def, mul_assoc]
      rw [heq]
      exact (cube H I k).mul_mem hcomm (face_mem_cube H hE hh)
    exact fun z hz => hle hz
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · exact hc g hg z
  · intro hz
    have hh := hc g⁻¹ ((H.level _).inv_mem hg) _ hz
    simpa [map_inv, mul_assoc] using hh

 
def commModulo (N : Subgroup G) (a : G) : Subgroup G where
  carrier := {b | b ∈ (Subgroup.normalizer (N : Set G)) ∧ ⁅a,b⁆ ∈ N}
  one_mem' := by simp
  mul_mem' := by
    rintro b c ⟨hb,hbc⟩ ⟨hc,hcc⟩
    change b ∈ Subgroup.normalizer (N : Set G) at hb
    change c ∈ Subgroup.normalizer (N : Set G) at hc
    refine ⟨Subgroup.mul_mem (Subgroup.normalizer (N : Set G)) hb hc, ?_⟩
    have hconj := (Subgroup.mem_normalizer_iff.mp hb ⁅a,c⁆).mp hcc
    have he : ⁅a,b*c⁆ = ⁅a,b⁆ * (b * ⁅a,c⁆ * b⁻¹) := by
      simp [commutatorElement_def, mul_assoc]
    rw [he]
    exact N.mul_mem hbc hconj
  inv_mem' := by
    rintro b ⟨hb,hbc⟩
    change b ∈ Subgroup.normalizer (N : Set G) at hb
    refine ⟨Subgroup.inv_mem (Subgroup.normalizer (N : Set G)) hb, ?_⟩
    have hconj := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (N : Set G)).inv_mem hb) (⁅a,b⁆)⁻¹).mp
      (N.inv_mem hbc)
    simpa [commutatorElement_def, mul_assoc] using hconj

lemma face_cube_commutator_mem (H : Filtration G) (I : Finset ι) {i j : ℕ}
    {D : Finset ι} (hD : D ⊆ I) {g : G} (hg : g ∈ H.level (D.card+i))
    {f : Finset ι → G} (hf : f ∈ cube H I j) :
    ⁅face D g, f⁆ ∈ cube H I (i+j) := by
  have hle : cube H I j ≤ commModulo (cube H I (i+j)) (face D g) := by
    refine iSup_le fun E => iSup_le fun hE => ?_
    rintro f ⟨h,hh,rfl⟩
    constructor
    · exact cube_normalizes H I _
        (cube_shift_le H I (Nat.zero_le j) (face_mem_cube H hE hh))
    · rw [face_commutator]
      have hdeg : (D ∪ E).card + (i+j) ≤ (D.card+i) + (E.card+j) := by
        have := Finset.card_union_le D E
        omega
      exact face_mem_cube H (Finset.union_subset hD hE)
        (H.antitone hdeg (H.commutator_le _ _ (Subgroup.commutator_mem_commutator hg hh)))
  exact (hle hf).2

lemma cube_commutator_mem (H : Filtration G) (I : Finset ι) {i j : ℕ}
    {f g : Finset ι → G} (hf : f ∈ cube H I i) (hg : g ∈ cube H I j) :
    ⁅f,g⁆ ∈ cube H I (i+j) := by
  have hle : cube H I i ≤ commModulo (cube H I (i+j)) g := by
    refine iSup_le fun D => iSup_le fun hD => ?_
    rintro f ⟨a,ha,rfl⟩
    constructor
    · exact cube_normalizes H I _
        (cube_shift_le H I (Nat.zero_le i) (face_mem_cube H hD ha))
    · have hh := face_cube_commutator_mem H I hD ha hg
      have hinv := (cube H I (i+j)).inv_mem hh
      simpa [commutatorElement_def, mul_assoc] using hinv
  have hinv := (cube H I (i+j)).inv_mem (hle hf).2
  simpa [commutatorElement_def, mul_assoc] using hinv

lemma cube_mono (H : Filtration G) {I J : Finset ι} (hIJ : I ⊆ J) (k : ℕ) :
    cube H I k ≤ cube H J k := by
  refine iSup_le fun D => iSup_le fun hD => ?_
  exact le_iSup_of_le D (le_iSup_of_le (hD.trans hIJ) le_rfl)

lemma upper_cube_mem (H : Filtration G) {I : Finset ι} {a : ι} (ha : a ∉ I) (k : ℕ)
    {f : Finset ι → G} (hf : f ∈ cube H I (k+1)) : upper a f ∈ cube H (insert a I) k := by
  have hle : cube H I (k+1) ≤ (cube H (insert a I) k).comap (upper a) := by
    refine iSup_le fun D => iSup_le fun hD => ?_
    rintro f ⟨g,hg,rfl⟩
    change upper a (face D g) ∈ cube H (insert a I) k
    rw [upper_face_apply]
    apply face_mem_cube H (Finset.insert_subset_insert a hD)
    have haD : a ∉ D := fun h => ha (hD h)
    change g ∈ H.level (D.card + (k+1)) at hg
    simpa only [Finset.card_insert_of_notMem haD, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hg
  exact hle hf

end CubeFaces

end
end
end
end

end OAI
