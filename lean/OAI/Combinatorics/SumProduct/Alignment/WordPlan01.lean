import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.AllLevel11
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
section
section
noncomputable section
open scoped BigOperators Topology ENNReal
open MeasureTheory Filter
end
 
end

section
 

 

noncomputable section
open scoped BigOperators Topology
open MeasureTheory Filter
namespace AllLevelFactorization.Factorization
open RationalLattice CubeFaces
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n s : ℕ} {c : RealCoordinates G n} {Γ : Subgroup G}
variable {K : Filtration G} {P : ℕ → ℤ → G} {L : ℕ → ℝ}
variable (F : Factorization c Γ s K P L)
variable (C : (r : Fin F.period) → F.ResidueCover r)
variable [∀ r,MeasurableSpace ((C r).CubeSpace (ι:=Empty))]
variable [∀ r,BorelSpace ((C r).CubeSpace (ι:=Empty))]
variable [MeasurableSpace (G⧸Γ)] [BorelSpace (G⧸Γ)] [CompactSpace (G⧸Γ)]
variable [SecondCountableTopology (G⧸Γ)]

def smoothAction : C(ℝ×(G⧸Γ),G⧸Γ) :=
  ⟨fun p=>F.smoothLimit p.1 • p.2,
    (F.smoothLimit_continuous.comp continuous_fst).smul continuous_snd⟩

def pointMixture : ProbabilityMeasure (G⧸Γ) :=
  letI : Nonempty (Fin F.period) := ⟨⟨0,F.period_pos⟩⟩
  ProbabilityMixtures.finiteAverage (fun r=>
    ProbabilityMixtures.intervalPush (C r).pointHaar F.smoothAction)

lemma pointMixture_integral (f : C(G⧸Γ,ℂ)) :
    (∫ y,f y ∂(F.pointMixture C : Measure _))=
      GlobalPointLaw.betaMixture (fun r=>(C r).pointHaar) (F.limitTest f) := by
  let : Nonempty (Fin F.period):=⟨⟨0,F.period_pos⟩⟩
  change (∫ y,f y ∂(ProbabilityMixtures.finiteAverage (fun r=>
    ProbabilityMixtures.intervalPush (C r).pointHaar F.smoothAction) : Measure _))=_
  rw [ProbabilityMixtures.finiteAverage_integral]
  · simp_rw [ProbabilityMixtures.intervalPush_integral]
    simp only [Fintype.card_fin,GlobalPointLaw.betaMixture,limitTest,leftTest,smoothAction,ContinuousMap.coe_mk]
  · intro r
    exact Integrable.of_bound f.continuous.aestronglyMeasurable ‖f‖
      (Eventually.of_forall f.norm_coe_le_norm)

variable [MeasurableSingletonClass (G⧸Γ)]

def empiricalPointLaw (N : ℕ) : ProbabilityMeasure (G⧸Γ) :=
  ProbabilityMixtures.empirical ⌊L (F.state.subseq N)⌋₊
    (fun k=>QuotientGroup.mk (P (F.state.subseq N) (k:ℤ)))

 

theorem weak_point_law (hL : ∀ N,0<L N) (ht : Tendsto L atTop atTop) :
    Tendsto F.empiricalPointLaw atTop (𝓝 (F.pointMixture C)) := by
  apply (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mpr
  intro f
  let ff : C(G⧸Γ,ℂ):=⟨f,f.continuous⟩
  have H:=F.global_point_law C hL ht ff
  rw [←F.pointMixture_integral C ff] at H
  apply H.congr'
  filter_upwards [(tendsto_nat_floor_atTop.comp
    (ht.comp F.state.strictmono.tendsto_atTop)).eventually (eventually_gt_atTop 0)] with N hN
  exact (ProbabilityMixtures.empirical_integral _ hN
    (fun k=>QuotientGroup.mk (P (F.state.subseq N) (k:ℤ))) ff).symm

end AllLevelFactorization.Factorization
end
 
end

section
 

 

namespace ConstructedWordPlan

 

open scoped commutatorElement
open scoped Pointwise

namespace CubeFaces

variable {G ι : Type*} [Group G] [DecidableEq ι]

 

structure Filtration (G : Type*) [Group G] where
  level : ℕ → Subgroup G
  antitone : Antitone level
  commutator_le : ∀ i j, ⁅level i, level j⁆ ≤ level (i + j)

 
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

namespace CubePolynomials
open _root_.OAI.ConstructedWordPlan.CubeFaces
noncomputable section
variable {G : Type*} [Group G]

def pattern (I : Finset ℕ) (h : ℕ → ℤ) (n : ℤ) : (ℤ → G) →* (Finset ℕ → G) where
  toFun f v := f (n + ∑ i ∈ v ∩ I, h i)
  map_one' := rfl
  map_mul' _ _ := rfl

def polynomials (H : Filtration G) (k : ℕ) : Subgroup (ℤ → G) :=
  ⨅ (I : Finset ℕ) (h : ℕ → ℤ) (n : ℤ), (cube H I k).comap (pattern I h n)

lemma mem_polynomials (H : Filtration G) (k : ℕ) (f : ℤ → G) :
    f ∈ polynomials H k ↔ ∀ I h n, pattern I h n f ∈ cube H I k := by
  simp [polynomials]

lemma polynomials_antitone (H : Filtration G) : Antitone (polynomials H) := by
  intro i j hij f hf
  rw [mem_polynomials] at hf ⊢
  intro I h n
  exact cube_shift_le H I hij (hf I h n)

lemma eval_mem {H : Filtration G} {k : ℕ} {f : ℤ → G}
    (hf : f ∈ polynomials H k) (n : ℤ) : f n ∈ H.level k := by
  have h := (mem_polynomials H k f).mp hf ∅ (fun _ => 0) n
  simpa [pattern] using cube_eval_mem H h ∅

lemma const_mem {H : Filtration G} {k : ℕ} {g : G} (hg : g ∈ H.level k) :
    (fun _ : ℤ => g) ∈ polynomials H k := by
  rw [mem_polynomials]
  intro I h n
  have he : pattern I h n (fun _ : ℤ => g) = face ∅ g := by ext v; simp [pattern, face]
  rw [he]
  exact face_mem_cube H (Finset.empty_subset I) (by simpa using hg)

lemma polynomials_eq_bot {H : Filtration G} {k : ℕ} (hk : H.level k = ⊥) :
    polynomials H k = ⊥ := by
  apply le_antisymm _ bot_le
  intro f hf
  apply Subgroup.mem_bot.mpr
  funext n
  have h := eval_mem hf n
  simpa [hk] using h

def shift (t : ℤ) : (ℤ → G) ≃* (ℤ → G) where
  toFun f n := f (n+t)
  invFun f n := f (n-t)
  left_inv f := by ext n; simp
  right_inv f := by ext n; simp
  map_mul' _ _ := rfl

lemma shift_mem {H : Filtration G} {k : ℕ} {f : ℤ → G}
    (hf : f ∈ polynomials H k) (t : ℤ) : shift t f ∈ polynomials H k := by
  rw [mem_polynomials] at hf ⊢
  intro I h n
  convert hf I h (n+t) using 1
  ext v
  change f ((n + ∑ i ∈ v ∩ I, h i) + t) = f ((n+t) + ∑ i ∈ v ∩ I, h i)
  congr 1
  ring

lemma derivative_mem {H : Filtration G} {k : ℕ} {f : ℤ → G}
    (hf : f ∈ polynomials H k) (t : ℤ) : f⁻¹ * shift t f ∈ polynomials H (k+1) := by
  rw [mem_polynomials] at hf ⊢
  intro I h n
  let a := I.sup id + 1
  have ha : a ∉ I := by
    intro ha
    have hle : a ≤ I.sup id := Finset.le_sup (f := id) ha
    dsimp [a] at hle
    omega
  let h' := Function.update h a t
  have hcube := hf (insert a I) h' n
  obtain ⟨l,hl,u,hu,he⟩ := cube_decompose H a I k hcube
  have heq : pattern I h n (f⁻¹ * shift t f) = u := by
    funext v
    let V := v ∩ I
    have hVI : V ⊆ I := Finset.inter_subset_right
    have haV : a ∉ V := fun h => ha (hVI h)
    have hs : ∑ j ∈ V, h' j = ∑ j ∈ V, h j := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjne : j ≠ a := by rintro rfl; exact haV hj
      exact Function.update_of_ne hjne t h
    have hVa : V ∩ insert a I = V := Finset.inter_eq_left.mpr (hVI.trans (Finset.subset_insert a I))
    have hVai : insert a V ∩ insert a I = insert a V :=
      Finset.inter_eq_left.mpr (Finset.insert_subset_insert a hVI)
    have hlo := congrFun he V
    have hhi := congrFun he (insert a V)
    change f (n + ∑ j ∈ V ∩ insert a I, h' j) = l V * (if a ∈ V then u V else 1) at hlo
    change f (n + ∑ j ∈ insert a V ∩ insert a I, h' j) =
      l (insert a V) * (if a ∈ insert a V then u (insert a V) else 1) at hhi
    simp only [hVa, haV, ite_false, mul_one, hs] at hlo
    simp only [hVai, Finset.mem_insert_self, ite_true,
      cube_insert_irrelevant H ha hl, cube_insert_irrelevant H ha hu,
      Finset.sum_insert haV, show h' a = t from Function.update_self a t h, hs] at hhi
    change (f (n + ∑ j ∈ V, h j))⁻¹ * f ((n + ∑ j ∈ V, h j) + t) = u v
    rw [show (n + ∑ j ∈ V, h j) + t = n + (t + ∑ j ∈ V, h j) by ring,
      hlo, hhi, inv_mul_cancel_left]
    exact cube_restrict H hu v
  rw [heq]
  exact hu

 

lemma mem_of_derivatives {H : Filtration G} {k : ℕ} {f : ℤ → G}
    (hvalue : ∀ n, f n ∈ H.level k)
    (hd : ∀ t, f⁻¹ * shift t f ∈ polynomials H (k+1)) : f ∈ polynomials H k := by
  rw [mem_polynomials]
  intro I
  induction I using Finset.induction_on with
  | empty =>
      intro h n
      have he : pattern ∅ h n f = face ∅ (f n) := by ext v; simp [pattern, face]
      rw [he]
      exact face_mem_cube H (Finset.empty_subset ∅) (by simpa using hvalue n)
  | @insert a I ha ih =>
      intro h n
      let l := pattern I h n f
      let u := pattern I h n (f⁻¹ * shift (h a) f)
      have hl : l ∈ cube H I k := ih h n
      have hu : u ∈ cube H I (k+1) := (mem_polynomials H (k+1) _).mp (hd (h a)) I h n
      have he : pattern (insert a I) h n f = l * upper a u := by
        funext v
        have haV : a ∉ v ∩ I := fun hh => ha (Finset.mem_inter.mp hh).2
        by_cases hav : a ∈ v
        · have hv : v ∩ insert a I = insert a (v ∩ I) := by
            ext b
            simp only [Finset.mem_inter, Finset.mem_insert]
            aesop
          change f (n + ∑ i ∈ v ∩ insert a I, h i) =
            f (n + ∑ i ∈ v ∩ I, h i) * (if a ∈ v then
              (f (n + ∑ i ∈ v ∩ I, h i))⁻¹ * f ((n + ∑ i ∈ v ∩ I, h i) + h a) else 1)
          rw [hv, Finset.sum_insert haV, ite_eq_left hav, mul_inv_cancel_left]
          congr 1
          ring
        · have hv : v ∩ insert a I = v ∩ I := by
            ext b
            simp only [Finset.mem_inter, Finset.mem_insert]
            aesop
          change f (n + ∑ i ∈ v ∩ insert a I, h i) =
            f (n + ∑ i ∈ v ∩ I, h i) * (if a ∈ v then u v else 1)
          rw [hv, ite_eq_right hav, mul_one]
      rw [he]
      exact (cube H (insert a I) k).mul_mem
        (cube_mono H (Finset.subset_insert a I) k hl) (upper_cube_mem H ha k hu)

lemma commutator_mem {H : Filtration G} {i j : ℕ} {f g : ℤ → G}
    (hf : f ∈ polynomials H i) (hg : g ∈ polynomials H j) :
    ⁅f,g⁆ ∈ polynomials H (i+j) := by
  rw [mem_polynomials] at hf hg ⊢
  intro I h n
  rw [map_commutatorElement]
  exact cube_commutator_mem H I (hf I h n) (hg I h n)

lemma normalizes (H : Filtration G) (k : ℕ) :
    polynomials H 0 ≤ (Subgroup.normalizer (polynomials H k)) := by
  intro f hf
  apply Subgroup.mem_normalizer_iff.mpr
  intro g
  have hconj {f : ℤ → G} (hf : f ∈ polynomials H 0) {g : ℤ → G}
      (hg : g ∈ polynomials H k) : f*g*f⁻¹ ∈ polynomials H k := by
    have hc : ⁅f,g⁆ ∈ polynomials H k := by simpa using commutator_mem hf hg
    have he : f*g*f⁻¹ = ⁅f,g⁆ * g := by simp [commutatorElement_def, mul_assoc]
    rw [he]
    exact (polynomials H k).mul_mem hc hg
  constructor
  · exact hconj hf
  · intro hg
    have hh := hconj ((polynomials H 0).inv_mem hf) hg
    simpa [mul_assoc] using hh

open _root_.Polynomial _root_.OAI.Polynomial in
lemma power_polynomial_mem {H : Filtration G} (e k : ℕ) (a : G)
    (ha : a ∈ H.level (e+k)) (p : ℤ[X]) (hp : p.natDegree ≤ e) :
    (fun n : ℤ => a ^ p.eval n) ∈ polynomials H k := by
  induction e generalizing k p with
  | zero =>
    have he : p = C (p.coeff 0) := eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero hp)
    rw [he]
    simp only [eval_C]
    apply const_mem
    simpa only [Nat.zero_add] using (H.level (0+k)).zpow_mem ha (p.coeff 0)
  | succ e ih =>
    apply mem_of_derivatives
    · intro n
      exact (H.level k).zpow_mem (H.antitone (Nat.le_add_left k (e+1)) ha) _
    · intro t
      let q := taylor t p - p
      have hq : q.natDegree ≤ e := by
        by_cases hp0 : p = 0
        · simp [q,hp0]
        by_cases hq0 : q = 0
        · simp [hq0]
        have hd : q.degree < p.degree :=
          degree_sub_lt_right (degree_taylor p t) hp0 (leadingCoeff_taylor t p)
        have hd' : q.natDegree < p.natDegree := (natDegree_lt_natDegree_iff hq0).mpr hd
        omega
      have ha' : a ∈ H.level (e+(k+1)) := by simpa only [Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using ha
      have h := ih (k+1) ha' q hq
      convert h using 1
      funext n
      change (a ^ p.eval n)⁻¹ * a ^ p.eval (n+t) = a ^ q.eval n
      rw [← zpow_neg, ← zpow_add]
      congr 1
      simp [q, taylor_apply, eval_comp]
      ring

end
end CubePolynomials

 

namespace FilteredPET
noncomputable section
open scoped Pointwise

section Multiset
variable {α : Type*} [DecidableEq α]

lemma decrease_of_high_embedding (degree : α → ℕ) (S T : Finset α)
    (a : α) (ha : a ∈ T) (f : α ↪ α)
    (hf : ∀ x, degree (f x) = degree x)
    (hhigh : ∀ x ∈ S, degree a ≤ degree x → x ∈ (T.erase a).map f) :
    Multiset.IsDershowitzMannaLT (S.val.map degree) (T.val.map degree) := by
  classical
  let H := S.filter (fun x => degree a ≤ degree x)
  let L := S.filter (fun x => ¬ degree a ≤ degree x)
  let U := H.val.map degree
  let V := L.val.map degree
  let W := (T.erase a).val.map degree
  have hH : H ⊆ (T.erase a).map f := by
    intro x hx
    exact hhigh x (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2
  have hUW : U ≤ W := by
    have h := Multiset.map_le_map (f := degree) (Finset.val_le_iff.mpr hH)
    simpa only [Finset.map_val, Multiset.map_map, Function.comp_def, hf] using h
  have hS : S.val.map degree = U + V := by
    have h := Multiset.filter_add_not (fun x => degree a ≤ degree x) S.val
    dsimp [U, V, H, L]
    rw [← Multiset.map_add]
    exact congrArg (Multiset.map degree) h.symm
  have hT : T.val.map degree = W + {degree a} := by
    have hv : T.val = a ::ₘ (T.erase a).val := (Multiset.cons_erase ha).symm
    rw [hv, Multiset.map_cons]
    change degree a ::ₘ (T.erase a).val.map degree = (T.erase a).val.map degree + {degree a}
    rw [add_comm, Multiset.singleton_add]
  refine ⟨U, V, (W - U) + {degree a}, by simp, hS, ?_, ?_⟩
  · rw [hT, ← add_assoc, add_tsub_cancel_of_le hUW]
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp hy
    refine ⟨degree a, by simp, ?_⟩
    exact Nat.lt_of_not_ge (Finset.mem_filter.mp hx).2

end Multiset

structure Filtration (G : Type*) [Group G] where
  level : ℕ → Subgroup G
  monotone : Monotone level
  zero : level 0 = ⊥
  exhaustive : ∀ g, ∃ d, g ∈ level d
  normal : ∀ d, (level d).Normal

namespace Filtration
variable {G : Type*} [Group G] (F : Filtration G)
instance level_normal (d : ℕ) : (F.level d).Normal := F.normal d

def degree (g : G) : ℕ := by
  classical
  exact Nat.find (F.exhaustive g)

lemma degree_mem (g : G) : g ∈ F.level (F.degree g) := by
  classical
  exact Nat.find_spec (F.exhaustive g)

lemma degree_le_iff (g : G) (d : ℕ) : F.degree g ≤ d ↔ g ∈ F.level d := by
  classical
  constructor
  · intro h
    exact F.monotone h (F.degree_mem g)
  · exact Nat.find_min' (F.exhaustive g)

@[simp] lemma degree_one : F.degree 1 = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact (F.degree_le_iff 1 0).mpr (by simp [F.zero])

@[simp] lemma degree_eq_zero (g : G) : F.degree g = 0 ↔ g = 1 := by
  rw [← Nat.le_zero, F.degree_le_iff, F.zero, Subgroup.mem_bot]

lemma degree_pos (g : G) : 0 < F.degree g ↔ g ≠ 1 := by
  rw [Nat.pos_iff_ne_zero, ne_eq, F.degree_eq_zero]

lemma degree_mul_le (g h : G) : F.degree (g*h) ≤ max (F.degree g) (F.degree h) := by
  apply (F.degree_le_iff _ _).mpr
  exact (F.level _).mul_mem (F.monotone (le_max_left _ _) (F.degree_mem g))
    (F.monotone (le_max_right _ _) (F.degree_mem h))

@[simp] lemma degree_inv (g : G) : F.degree g⁻¹ = F.degree g := by
  apply le_antisymm
  · exact (F.degree_le_iff _ _).mpr ((F.level _).inv_mem (F.degree_mem g))
  · exact (F.degree_le_iff _ _).mpr (by simpa using (F.level _).inv_mem (F.degree_mem g⁻¹))

abbrev Signature := Σ d : ℕ, G ⧸ F.level (d-1)

def signature (g : G) : F.Signature :=
  ⟨F.degree g, QuotientGroup.mk' (F.level (F.degree g - 1)) g⟩

lemma signature_at (g : G) (d : ℕ) (h : F.degree g = d) :
    F.signature g = ⟨d, QuotientGroup.mk' (F.level (d-1)) g⟩ := by
  subst d
  rfl

lemma degree_mul_eq_left {g h : G} (hh : F.degree h < F.degree g) :
    F.degree (g*h) = F.degree g := by
  apply le_antisymm
  · exact (F.degree_mul_le g h).trans (max_le le_rfl hh.le)
  · by_contra H
    have H' : F.degree (g*h) ≤ F.degree g - 1 := by omega
    have Hh : F.degree h ≤ F.degree g - 1 := by omega
    have hg : g ∈ F.level (F.degree g - 1) := by
      have := (F.level _).mul_mem ((F.degree_le_iff _ _).mp H')
        ((F.level _).inv_mem ((F.degree_le_iff _ _).mp Hh))
      simpa only [mul_inv_cancel_right] using this
    have := (F.degree_le_iff _ _).mpr hg
    omega

lemma degree_eq_of_lower {f g : G} (h : f*g⁻¹ ∈ F.level (F.degree g - 1)) :
    F.degree f = F.degree g := by
  by_cases hg : g = 1
  · subst g
    simpa [F.zero] using h
  have hd : 0 < F.degree g := (F.degree_pos g).mpr hg
  have hfg : F.degree f ≤ F.degree g := by
    apply (F.degree_le_iff _ _).mpr
    have hprod := (F.level _).mul_mem
      (F.monotone (Nat.sub_le _ _) h) (F.degree_mem g)
    simpa only [inv_mul_cancel_right] using hprod
  apply le_antisymm hfg
  by_contra H
  have H' : F.degree f ≤ F.degree g - 1 := by omega
  have hgv : g ∈ F.level (F.degree g - 1) := by
    have hprod := (F.level _).mul_mem ((F.level _).inv_mem h)
      ((F.degree_le_iff _ _).mp H')
    simpa only [mul_inv_rev, inv_inv, mul_assoc, inv_mul_cancel, mul_one] using hprod
  have := (F.degree_le_iff _ _).mpr hgv
  omega

lemma signature_eq_of_lower {f g : G} (h : f*g⁻¹ ∈ F.level (F.degree g - 1)) :
    F.signature f = F.signature g := by
  have hd := F.degree_eq_of_lower h
  rw [F.signature_at f (F.degree g) hd]
  change (⟨F.degree g, QuotientGroup.mk' (F.level (F.degree g-1)) f⟩ : F.Signature) =
    ⟨F.degree g, QuotientGroup.mk' (F.level (F.degree g-1)) g⟩
  congr 1
  apply (mul_inv_eq_one).mp
  rw [← map_inv, ← map_mul]
  change ((f*g⁻¹ : G) : G ⧸ F.level (F.degree g-1)) = 1
  simpa only [QuotientGroup.eq_one_iff] using h

 

def leaderShift (d : ℕ) (a : G) : F.Signature ≃ F.Signature where
  toFun x := ⟨x.1, if x.1 = d then x.2 *
    (QuotientGroup.mk' (F.level (x.1-1)) a)⁻¹ else x.2⟩
  invFun x := ⟨x.1, if x.1 = d then x.2 *
    QuotientGroup.mk' (F.level (x.1-1)) a else x.2⟩
  left_inv := by rintro ⟨k,x⟩; by_cases hk : k = d <;> simp [hk]
  right_inv := by rintro ⟨k,x⟩; by_cases hk : k = d <;> simp [hk]

@[simp] lemma leaderShift_degree (d : ℕ) (a : G) (x : F.Signature) :
    (F.leaderShift d a x).1 = x.1 := rfl

lemma quotient_eq_one_iff (d : ℕ) (g : G) :
    QuotientGroup.mk' (F.level d) g = 1 ↔ F.degree g ≤ d := by
  change (g : G ⧸ F.level d) = 1 ↔ F.degree g ≤ d
  rw [QuotientGroup.eq_one_iff, F.degree_le_iff]

lemma signature_mul_high {g a : G} (ha : F.degree a < F.degree g) :
    F.signature (g*a⁻¹) = F.signature g := by
  apply F.signature_eq_of_lower
  have ha' : a⁻¹ ∈ F.level (F.degree g - 1) := by
    apply (F.level _).inv_mem
    exact (F.degree_le_iff _ _).mp (by omega)
  exact (F.normal _).conj_mem _ ha' g

lemma signature_mul_equal {g a : G} (hg : F.degree g = F.degree a) (h : F.degree a ≤ F.degree (g*a⁻¹)) :
    F.signature (g*a⁻¹) = F.leaderShift (F.degree a) a (F.signature g) := by
  have hd : F.degree (g*a⁻¹) = F.degree a :=
    le_antisymm (by simpa [hg] using F.degree_mul_le g a⁻¹) h
  rw [F.signature_at (g*a⁻¹) (F.degree a) hd,
    F.signature_at g (F.degree a) hg]
  change (⟨F.degree a, QuotientGroup.mk' (F.level (F.degree a-1)) (g*a⁻¹)⟩ : F.Signature) =
    ⟨F.degree a, if F.degree a = F.degree a then
      QuotientGroup.mk' (F.level (F.degree a-1)) g *
      (QuotientGroup.mk' (F.level (F.degree a-1)) a)⁻¹ else
      QuotientGroup.mk' (F.level (F.degree a-1)) g⟩
  simp only [ite_true, map_mul, map_inv]

lemma signature_eq_lower {f g : G} (h : F.signature f = F.signature g) :
    f*g⁻¹ ∈ F.level (F.degree g-1) := by
  have hd : F.degree f = F.degree g := congrArg Sigma.fst h
  rw [F.signature_at f (F.degree g) hd] at h
  have hq : QuotientGroup.mk' (F.level (F.degree g-1)) f =
      QuotientGroup.mk' (F.level (F.degree g-1)) g := eq_of_heq (Sigma.mk.inj h).2
  apply (QuotientGroup.eq_one_iff _).mp
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  change QuotientGroup.mk' (F.level (F.degree g-1)) f *
    (QuotientGroup.mk' (F.level (F.degree g-1)) g)⁻¹ = 1
  rw [hq, mul_inv_cancel]

 

lemma reduction_signature {q p a : G} (hmin : F.degree a ≤ F.degree p)
    (hd : q*a*p⁻¹ ∈ F.level (F.degree p-1))
    (hq : F.degree a ≤ F.degree q) :
    F.signature q = F.leaderShift (F.degree a) a (F.signature p) := by
  have hs : F.signature (q*a) = F.signature p := F.signature_eq_of_lower hd
  have hdeg : F.degree (q*a) = F.degree p := congrArg Sigma.fst hs
  rcases lt_or_eq_of_le hmin with hlt | heq
  · have hh : F.signature ((q*a)*a⁻¹) = F.signature (q*a) :=
      F.signature_mul_high (by omega)
    rw [show (q*a)*a⁻¹ = q by group, hs] at hh
    rw [hh]
    simp only [leaderShift, signature, Equiv.coe_fn_mk, ite_eq_right (Nat.ne_of_gt hlt)]
  · have hh := F.signature_mul_equal (g := q*a) (a := a) (hdeg.trans heq.symm)
      (by simpa only [mul_inv_cancel_right] using hq)
    simpa only [mul_inv_cancel_right, hs] using hh

lemma reduction_same {q p a : G} (ha : 0 < F.degree a)
    (hp : F.signature p = F.signature a)
    (hd : q*a*p⁻¹ ∈ F.level (F.degree p-1)) : F.degree q < F.degree a := by
  have he : F.degree p = F.degree a := congrArg Sigma.fst hp
  have hpa := F.signature_eq_lower hp
  have hmul := (F.level (F.degree a-1)).mul_mem (he ▸ hd) hpa
  have hconj : q ∈ F.level (F.degree a-1) := by
    rwa [show (q*a*p⁻¹)*(p*a⁻¹) = q by group] at hmul
  have hh := (F.degree_le_iff q _).mpr hconj
  omega

def leaders (P : Finset G) : Finset F.Signature := by
  classical
  exact (P.erase 1).image F.signature

def weight (P : Finset G) : Multiset ℕ := (F.leaders P).val.map Sigma.fst

 

theorem weight_lt (P Q : Finset G) (a : G) (haP : a ∈ P) (ha : a ≠ 1)
    (hmin : ∀ p ∈ P, F.degree a ≤ F.degree p)
    (hQ : ∀ q ∈ Q, ∃ p ∈ P, q*a*p⁻¹ ∈ F.level (F.degree p-1)) :
    Multiset.IsDershowitzMannaLT (F.weight Q) (F.weight P) := by
  classical
  have hapos := (F.degree_pos a).mpr ha
  have hamem : F.signature a ∈ F.leaders P :=
    Finset.mem_image.mpr ⟨a, Finset.mem_erase.mpr ⟨ha,haP⟩,rfl⟩
  apply decrease_of_high_embedding Sigma.fst (F.leaders Q) (F.leaders P)
    (F.signature a) hamem (F.leaderShift (F.degree a) a).toEmbedding
    (F.leaderShift_degree _ _)
  intro x hx hxhigh
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨p,hp,hd⟩ := hQ q (Finset.mem_erase.mp hq).2
  have hplead : F.signature p ≠ F.signature a := by
    intro heq
    exact (Nat.not_le_of_gt (F.reduction_same hapos heq hd)) hxhigh
  apply Finset.mem_map.mpr
  refine ⟨F.signature p, Finset.mem_erase.mpr ⟨hplead, ?_⟩, ?_⟩
  · apply Finset.mem_image.mpr
    refine ⟨p, Finset.mem_erase.mpr ⟨?_,hp⟩,rfl⟩
    intro hh
    have := hmin p hp
    simp only [hh, F.degree_one] at this
    omega
  · exact (F.reduction_signature (hmin p hp) hd hxhigh).symm

end Filtration
end
end FilteredPET
namespace GroupPET
noncomputable section
variable (G S : Type*) [Group G] [Group S]

 

structure System where
  filtration : FilteredPET.Filtration S
  eval : ℤ → S →* G
  eval_zero : ∀ p, eval 0 p = 1
  shift : S → ℤ → S
  shift_eval : ∀ p n k, eval k (shift p n) = (eval n p)⁻¹ * eval (n+k) p
  shift_lower : ∀ p n, shift p n * p⁻¹ ∈ filtration.level (filtration.degree p-1)
  conjugate : G → S → S
  conjugate_eval : ∀ g p k, eval k (conjugate g p) = g⁻¹ * eval k p * g
  conjugate_lower : ∀ g p, conjugate g p * p⁻¹ ∈ filtration.level (filtration.degree p-1)

variable {G S}
namespace System
variable (T : System G S)

def reduce (p a : S) (n : ℤ) : S := T.shift p n * a⁻¹

def reducedFamily (P : Finset S) (a : S) (I : Finset ℤ) : Finset S := by
  classical
  exact (P ×ˢ I).image (fun pn => T.reduce pn.1 a pn.2)

lemma reduce_eval (p a : S) (n k : ℤ) :
    T.eval k (T.reduce p a n) = (T.eval n p)⁻¹ * T.eval (n+k) p * (T.eval k a)⁻¹ := by
  simp only [reduce, map_mul, map_inv, T.shift_eval]

lemma reducedFamily_weight_lt (P : Finset S) (a : S) (I : Finset ℤ)
    (haP : a ∈ P) (ha : a ≠ 1)
    (hmin : ∀ p ∈ P, T.filtration.degree a ≤ T.filtration.degree p) :
    Multiset.IsDershowitzMannaLT (T.filtration.weight (T.reducedFamily P a I))
      (T.filtration.weight P) := by
  classical
  apply T.filtration.weight_lt P _ a haP ha hmin
  intro q hq
  obtain ⟨⟨p,n⟩,hpn,rfl⟩ := Finset.mem_image.mp hq
  refine ⟨p,(Finset.mem_product.mp hpn).1,?_⟩
  simpa only [reduce, inv_mul_cancel_right] using T.shift_lower p n

lemma conjugate_signature (g : G) (p : S) :
    T.filtration.signature (T.conjugate g p) = T.filtration.signature p :=
  T.filtration.signature_eq_of_lower (T.conjugate_lower g p)

lemma conjugate_eq_one_iff (g : G) (p : S) : T.conjugate g p = 1 ↔ p = 1 := by
  have hd : T.filtration.degree (T.conjugate g p) = T.filtration.degree p :=
    congrArg Sigma.fst (T.conjugate_signature g p)
  rw [← T.filtration.degree_eq_zero, ← T.filtration.degree_eq_zero, hd]

def conjugateFamily (P : Finset S) (I : Finset G) : Finset S := by
  classical
  exact (P ×ˢ I).image (fun pg => T.conjugate pg.2 pg.1)

lemma conjugateFamily_leaders (P : Finset S) (I : Finset G) (hI : I.Nonempty) :
    T.filtration.leaders (T.conjugateFamily P I) = T.filtration.leaders P := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨⟨p,g⟩,hpg,rfl⟩ := Finset.mem_image.mp (Finset.mem_erase.mp hq).2
    rw [T.conjugate_signature]
    apply Finset.mem_image.mpr
    refine ⟨p, Finset.mem_erase.mpr ⟨?_,(Finset.mem_product.mp hpg).1⟩,rfl⟩
    exact (T.conjugate_eq_one_iff g p).not.mp (Finset.mem_erase.mp hq).1
  · intro hx
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨g,hg⟩ := hI
    apply Finset.mem_image.mpr
    refine ⟨T.conjugate g p, Finset.mem_erase.mpr ⟨?_,?_⟩, T.conjugate_signature g p⟩
    · exact (T.conjugate_eq_one_iff g p).not.mpr (Finset.mem_erase.mp hp).1
    · exact Finset.mem_image.mpr ⟨(p,g), Finset.mem_product.mpr
        ⟨(Finset.mem_erase.mp hp).2,hg⟩,rfl⟩

lemma conjugateFamily_weight (P : Finset S) (I : Finset G) (hI : I.Nonempty) :
    T.filtration.weight (T.conjugateFamily P I) = T.filtration.weight P := by
  simp only [FilteredPET.Filtration.weight, T.conjugateFamily_leaders P I hI]

end System
end
end GroupPET
namespace MinimalSubsystem
variable {M X : Type*} [Monoid M] [TopologicalSpace X] [MulAction M X]
  [ContinuousConstSMul M X] [CompactSpace X] [Nonempty X]

omit [ContinuousConstSMul M X] in
@[to_additive exists_closed_minimal_add]
theorem exists_closed_minimal :
    ∃ S : Set X, Minimal (fun A : Set X =>
      IsClosed A ∧ A.Nonempty ∧ ∀ g : M, ∀ x ∈ A, g • x ∈ A) S := by
  classical
  let F : Set (Set X) := {A | IsClosed A ∧ A.Nonempty ∧ ∀ g : M, ∀ x ∈ A, g • x ∈ A}
  have H : ∀ c ⊆ F, IsChain (· ⊆ ·) c → c.Nonempty →
      ∃ lb ∈ F, ∀ A ∈ c, lb ⊆ A := by
    intro c hc hchain hne
    have : Nonempty c := hne.to_subtype
    refine ⟨⋂₀ c, ⟨?_, ?_, ?_⟩, fun A hA => Set.sInter_subset_of_mem hA⟩
    · exact isClosed_sInter (fun A hA => (hc hA).1)
    · exact IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed
        (by
          intro A hA B hB
          rcases hchain.total hA hB with hAB | hBA
          · exact ⟨A, hA, Set.Subset.rfl, hAB⟩
          · exact ⟨B, hB, hBA, Set.Subset.rfl⟩) (fun A hA => (hc hA).2.1)
        (fun A hA => (hc hA).1.isCompact) (fun A hA => (hc hA).1)
    · intro g x hx
      apply Set.mem_sInter.mpr
      intro A hA
      exact (hc hA).2.2 g x (Set.mem_sInter.mp hx A hA)
  obtain ⟨S, _, hS⟩ := zorn_superset_nonempty F H Set.univ
    ⟨isClosed_univ, Set.univ_nonempty, by simp⟩
  exact ⟨S, hS⟩

@[to_additive exists_minimal_subaddaction]
theorem exists_minimal_subaction :
    ∃ S : SubMulAction M X, IsClosed (S : Set X) ∧ Nonempty S ∧ MulAction.IsMinimal M S := by
  classical
  obtain ⟨A, hA⟩ := exists_closed_minimal (M := M) (X := X)
  let S : SubMulAction M X := ⟨A, fun g _ hx => hA.1.2.2 g _ hx⟩
  have hSc : IsClosed (S : Set X) := hA.1.1
  have : ContinuousConstSMul M S := ⟨fun g =>
    ((continuous_const_smul g).comp continuous_subtype_val).subtype_mk _⟩
  refine ⟨S, hSc, hA.1.2.1.to_subtype, ?_⟩
  apply (isMinimal_iff_isClosed_smul_invariant M (α := S)).mpr
  intro B hBc hBinv
  rcases B.eq_empty_or_nonempty with hBe | hBne
  · exact Or.inl hBe
  · right
    have hImg : IsClosed (Subtype.val '' B : Set X) ∧
        (Subtype.val '' B : Set X).Nonempty ∧
        ∀ g : M, ∀ x ∈ (Subtype.val '' B : Set X), g • x ∈ (Subtype.val '' B : Set X) := by
      refine ⟨hSc.isClosedMap_subtype_val B hBc, hBne.image _, ?_⟩
      intro g x hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨g • y, hBinv g ⟨y,hy,rfl⟩, rfl⟩
    have hsub : (Subtype.val '' B : Set X) ⊆ A := by
      rintro x ⟨y, _, rfl⟩
      exact y.2
    have hEq := hA.eq_of_le hImg hsub
    apply Set.eq_univ_of_forall
    intro x
    have hx : (x : X) ∈ (Subtype.val '' B : Set X) := by rw [hEq]; exact x.2
    obtain ⟨y, hy, heq⟩ := hx
    exact (Subtype.ext heq) ▸ hy

end MinimalSubsystem

namespace GroupPETRecurrence
open GroupPET System
noncomputable section
variable {G S X : Type*} [Group G] [Group S] [TopologicalSpace X] [MulAction G X]
  [ContinuousConstSMul G X] (T : System G S)

 

def ClopenRecurrence (P : Finset S) : Prop :=
  ∀ U : Set X, IsClopen U → U.Nonempty → ∀ N : ℕ,
    ∃ k : ℕ, N < k ∧ ∃ x ∈ U, ∀ p ∈ P, T.eval (k : ℤ) p • x ∈ U

variable {C : Type*} [Fintype C] [TopologicalSpace C] [DiscreteTopology C]

def Focused (P : Finset S) (χ : X → C) (N : ℕ) {n : ℕ}
    (t : Fin n → ℕ) (x : Fin n → X) : Prop :=
  (∀ i j, i < j → N + t i < t j) ∧
    ∀ i j, i ≤ j → ∀ p ∈ P,
      χ (T.eval ((t j : ℤ) - (t i : ℤ)) p • x j) = χ (x i)

omit [TopologicalSpace X] [ContinuousConstSMul G X] [Fintype C]
  [TopologicalSpace C] [DiscreteTopology C] in
lemma Focused.monotone {P : Finset S} {χ : X → C} {N n : ℕ}
    {t : Fin n → ℕ} {x : Fin n → X} (h : Focused T P χ N t x) : Monotone t := by
  intro i j hij
  rcases lt_or_eq_of_le hij with hlt | rfl
  · exact le_trans (Nat.le_add_left _ _) (h.1 i j hlt).le
  · rfl

omit [TopologicalSpace X] [ContinuousConstSMul G X] [Fintype C]
  [TopologicalSpace C] [DiscreteTopology C] in
lemma focused_singleton (P : Finset S) (χ : X → C) (N : ℕ)
    (hP : ∀ p ∈ P, T.eval 0 p = 1) (x : X) :
    Focused T P χ N (fun _ : Fin 1 => 0) (fun _ => x) := by
  constructor
  · intro i j hij
    have : i = j := Subsingleton.elim _ _
    subst j
    exact (lt_irrefl _ hij).elim
  · intro i j _ p hp
    simp [hP p hp]

omit [Fintype C] in
 
lemma focused_extend (P : Finset S) (p₀ : S)
    (hP : ∀ p ∈ P, T.eval 0 p = 1)
    (ih : ∀ I : Finset ℤ, ClopenRecurrence T (X := X) (T.reducedFamily P p₀ I))
    (χ : X → C) (hχ : Continuous χ) (N n : ℕ)
    (t : Fin (n+1) → ℕ) (x : Fin (n+1) → X) (hf : Focused T P χ N t x) :
    ∃ (t' : Fin (n+2) → ℕ) (x' : Fin (n+2) → X), Focused T P χ N t' x' := by
  classical
  let lastTime := t (Fin.last n)
  let offsets : Fin (n+1) → ℤ := fun i => (lastTime : ℤ) - (t i : ℤ)
  let I := Finset.univ.image offsets
  let Q := T.reducedFamily P p₀ I
  let profile : X → (Fin (n+1) × {p // p ∈ P} → C) :=
    fun y ip => χ (T.eval (offsets ip.1) ip.2.1 • y)
  have hprofile : Continuous profile := by
    apply continuous_pi
    intro ip
    exact hχ.comp (continuous_const_smul _)
  let U := profile ⁻¹' {profile (x (Fin.last n))}
  have hU : IsClopen U := (isClopen_discrete _).preimage hprofile
  have hxU : x (Fin.last n) ∈ U := rfl
  obtain ⟨k, hk, y, hy, hyQ⟩ := ih I U hU ⟨_, hxU⟩ N
  let time := lastTime + k
  let point := (T.eval (k : ℤ) p₀)⁻¹ • y
  refine ⟨Fin.snoc t time, Fin.snoc x point, ?_, ?_⟩
  · intro i j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · refine Fin.lastCases ?_ (fun i => ?_) i
      · intro hij
        exact (lt_irrefl _ hij).elim
      · intro _
        simp only [Fin.snoc_castSucc, Fin.snoc_last]
        have hti := Focused.monotone T hf (Fin.le_last i)
        change t i ≤ lastTime at hti
        omega
    · refine Fin.lastCases ?_ (fun i => ?_) i
      · intro hij
        exact (not_lt_of_ge (Fin.le_last _) hij).elim
      · intro hij
        simp only [Fin.snoc_castSucc]
        exact hf.1 i j (by simpa using hij)
  · intro i j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · refine Fin.lastCases ?_ (fun i => ?_) i
      · intro _ p hp
        simp only [Fin.snoc_last, sub_self, hP p hp, one_smul]
      · intro _ p hp
        simp only [Fin.snoc_castSucc, Fin.snoc_last]
        have hqQ : T.reduce p p₀ (offsets i) ∈ Q := by
          apply Finset.mem_image.mpr
          refine ⟨(p, offsets i), Finset.mem_product.mpr ⟨hp, ?_⟩, rfl⟩
          exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
        have hcolor := congrFun (hyQ _ hqQ) (i, ⟨p,hp⟩)
        change χ (T.eval (offsets i) p •
          (T.eval (k : ℤ) (T.reduce p p₀ (offsets i)) • y)) =
          χ (T.eval (offsets i) p • x (Fin.last n)) at hcolor
        rw [hf.2 i (Fin.last n) (Fin.le_last i) p hp] at hcolor
        convert hcolor using 1
        dsimp [point]
        rw [← mul_smul, ← mul_smul]
        congr 2
        rw [T.reduce_eval]
        have harg : ((time : ℕ) : ℤ) - (t i : ℤ) = offsets i + (k : ℤ) := by
          dsimp [time, offsets]
          ring
        rw [harg]
        group
    · refine Fin.lastCases ?_ (fun i => ?_) i
      · intro hij
        have := Fin.last_le_iff.mp hij
        exact (Fin.castSucc_ne_last j this).elim
      · intro hij p hp
        simp only [Fin.snoc_castSucc]
        exact hf.2 i j (by simpa using hij) p hp

omit [Fintype C] in
lemma focused_arbitrary [Nonempty X] (P : Finset S) (p₀ : S)
    (hP : ∀ p ∈ P, T.eval 0 p = 1)
    (ih : ∀ I : Finset ℤ, ClopenRecurrence T (X := X) (T.reducedFamily P p₀ I))
    (χ : X → C) (hχ : Continuous χ) (N n : ℕ) :
    ∃ (t : Fin (n+1) → ℕ) (x : Fin (n+1) → X), Focused T P χ N t x := by
  induction n with
  | zero =>
    exact ⟨_, _, focused_singleton T P χ N hP (Classical.choice inferInstance)⟩
  | succ n ihn =>
    obtain ⟨t, x, hf⟩ := ihn
    exact focused_extend T P p₀ hP ih χ hχ N n t x hf

lemma monochromatic_of_lower [Nonempty X] (P : Finset S) (p₀ : S)
    (hP : ∀ p ∈ P, T.eval 0 p = 1)
    (ih : ∀ I : Finset ℤ, ClopenRecurrence T (X := X) (T.reducedFamily P p₀ I))
    (χ : X → C) (hχ : Continuous χ) (N : ℕ) :
    ∃ k : ℕ, N < k ∧ ∃ x : X, ∀ p ∈ P, χ (T.eval (k : ℤ) p • x) = χ x := by
  classical
  obtain ⟨t, x, hf⟩ := focused_arbitrary T P p₀ hP ih χ hχ N (Fintype.card C)
  have hni : ¬Function.Injective (fun i => χ (x i)) := by
    intro hinj
    have hcard := Fintype.card_le_of_injective _ hinj
    simp only [Fintype.card_fin] at hcard
    omega
  obtain ⟨i, j, heq, hne⟩ := Function.not_injective_iff.mp hni
  have finish (i j : Fin (Fintype.card C + 1)) (hij : i < j) (heq : χ (x i) = χ (x j)) :
      ∃ k : ℕ, N < k ∧ ∃ x : X, ∀ p ∈ P, χ (T.eval (k : ℤ) p • x) = χ x := by
    have htimes := hf.1 i j hij
    refine ⟨t j - t i, by omega, x j, ?_⟩
    intro p hp
    rw [Nat.cast_sub (Focused.monotone T hf hij.le)]
    exact (hf.2 i j hij.le p hp).trans heq
  rcases lt_or_gt_of_ne hne with hij | hji
  · exact finish i j hij heq
  · exact finish j i hji heq.symm

 

theorem clopen_polynomial_recurrence [CompactSpace X] [MulAction.IsMinimal G X]
    (P : Finset S) : ClopenRecurrence T (X := X) P := by
  classical
  suffices H : ∀ w : Multiset ℕ, ∀ P : Finset S, T.filtration.weight P = w →
      ClopenRecurrence T (X := X) P from H (T.filtration.weight P) P rfl
  intro w
  apply (Multiset.wellFounded_isDershowitzMannaLT (α := ℕ)).induction w
  intro w ih P hw
  let A := P.erase 1
  have hwA : T.filtration.weight A = w := by
    simpa [FilteredPET.Filtration.weight, FilteredPET.Filtration.leaders,A] using hw
  have hrecA : ClopenRecurrence T (X := X) A := by
    intro U hU hUne N
    have : Nonempty X := ⟨hUne.choose⟩
    by_cases hA : A.Nonempty
    · obtain ⟨I,hI⟩ := isCompact_univ.elim_finite_subcover
        (fun g : G => (g • ·) ⁻¹' U)
        (fun g => hU.2.preimage (continuous_const_smul g))
        (by rw [hU.2.iUnion_preimage_smul G hUne])
      let Q := T.conjugateFamily A (insert 1 I)
      have hwQ : T.filtration.weight Q = w :=
        (T.conjugateFamily_weight A _ (Finset.insert_nonempty 1 I)).trans hwA
      have hQ : Q.Nonempty := by
        obtain ⟨p,hp⟩ := hA
        exact ⟨T.conjugate 1 p, Finset.mem_image.mpr ⟨(p,1),
          Finset.mem_product.mpr ⟨hp,Finset.mem_insert_self 1 I⟩,rfl⟩⟩
      obtain ⟨a,ha,hmin⟩ := Q.exists_min_image T.filtration.degree hQ
      have ha1 : a ≠ 1 := by
        obtain ⟨⟨p,g⟩,hpg,rfl⟩ := Finset.mem_image.mp ha
        exact (T.conjugate_eq_one_iff g p).not.mpr
          (Finset.mem_erase.mp (Finset.mem_product.mp hpg).1).1
      let χ : X → (I → Fin 2) := fun x g =>
        LocallyConstant.ofIsClopen (hU.preimage (continuous_const_smul (g : G))) x
      have hχ : Continuous χ := continuous_pi fun _ => LocallyConstant.continuous _
      have hsmall : ∀ J : Finset ℤ, ClopenRecurrence T (X := X) (T.reducedFamily Q a J) := by
        intro J
        exact ih _ (hwQ ▸ T.reducedFamily_weight_lt Q a J ha ha1 hmin) _ rfl
      obtain ⟨k,hk,x,hx⟩ := monochromatic_of_lower T Q a (fun p _ => T.eval_zero p)
        hsmall χ hχ N
      obtain ⟨g,hgI,hgx⟩ := Set.mem_iUnion₂.mp (hI (Set.mem_univ x))
      have hmem (y : X) : χ y ⟨g,hgI⟩ = 0 ↔ g • y ∈ U := by
        simp [χ, LocallyConstant.ofIsClopen]
      refine ⟨k,hk,g • x,hgx,?_⟩
      intro p hp
      have hq : T.conjugate g p ∈ Q := Finset.mem_image.mpr
        ⟨(p,g),Finset.mem_product.mpr ⟨hp,Finset.mem_insert_of_mem hgI⟩,rfl⟩
      have hcolor := congrFun (hx _ hq) ⟨g,hgI⟩
      have hpy := (hmem _).mp (hcolor.trans ((hmem x).mpr hgx))
      rw [T.conjugate_eval] at hpy
      simpa only [mul_smul, inv_smul_smul, smul_inv_smul] using hpy
    · obtain ⟨x,hx⟩ := hUne
      refine ⟨N+1,Nat.lt_succ_self _,x,hx,?_⟩
      intro p hp
      exact (hA ⟨p,hp⟩).elim
  intro U hU hUne N
  obtain ⟨k,hk,x,hx,hAx⟩ := hrecA U hU hUne N
  refine ⟨k,hk,x,hx,?_⟩
  intro p hp
  by_cases hp1 : p = 1
  · simpa [hp1] using hx
  · exact hAx p (Finset.mem_erase.mpr ⟨hp1,hp⟩)

omit [Fintype C] in
 

theorem continuous_polynomial_recurrence [CompactSpace X] [Nonempty X]
    (P : Finset S)
    (χ : X → C) (hχ : Continuous χ) (N : ℕ) :
    ∃ k : ℕ, N < k ∧ ∃ x : X, ∀ p ∈ P, χ (T.eval (k : ℤ) p • x) = χ x := by
  classical
  obtain ⟨S,hSc,hSne,hSmin⟩ :=
    MinimalSubsystem.exists_minimal_subaction (M := G) (X := X)
  have : Nonempty S := hSne
  have : CompactSpace S := isCompact_iff_compactSpace.mp hSc.isCompact
  have : MulAction.IsMinimal G S := hSmin
  have : ContinuousConstSMul G S := ⟨fun g =>
    ((continuous_const_smul g).comp continuous_subtype_val).subtype_mk _⟩
  let x : S := Classical.choice hSne
  let U : Set S := (fun y : S => χ y) ⁻¹' {χ x}
  have hU : IsClopen U := (isClopen_discrete _).preimage (hχ.comp continuous_subtype_val)
  have hx : x ∈ U := rfl
  obtain ⟨k,hk,y,hy,hPy⟩ := clopen_polynomial_recurrence T P U hU ⟨x,hx⟩ N
  refine ⟨k,hk,y,?_⟩
  intro p hp
  exact (hPy p hp).trans hy.symm

omit [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X] in
 

theorem coloring_polynomial_recurrence
    (P : Finset S)
    (χ : G → C) (N : ℕ) :
    ∃ k : ℕ, N < k ∧ ∃ a : G, ∀ p ∈ P, χ (T.eval (k : ℤ) p * a) = χ a := by
  classical
  let : MulAction G (G → C) := {
    smul := fun a f b => f (b*a)
    one_smul := fun f => by
      funext b
      exact congrArg f (mul_one b)
    mul_smul := fun a b f => by
      funext c
      exact congrArg f (mul_assoc c a b).symm }
  have : ContinuousConstSMul G (G → C) := ⟨fun a =>
    continuous_pi fun b => continuous_apply (b*a)⟩
  let S : SubMulAction G (G → C) := {
    carrier := closure (MulAction.orbit G χ)
    smul_mem' := fun a f hf => smul_closure_orbit_subset a χ ⟨f,hf,rfl⟩ }
  have hSclosed : IsClosed (S : Set (G → C)) := isClosed_closure
  have : CompactSpace S := isCompact_iff_compactSpace.mp hSclosed.isCompact
  have : Nonempty S := ⟨⟨χ,subset_closure (MulAction.mem_orbit_self χ)⟩⟩
  have : ContinuousConstSMul G S := ⟨fun a =>
    ((continuous_const_smul a).comp continuous_subtype_val).subtype_mk _⟩
  let eval₀ : S → C := fun f => f.1 1
  have heval : Continuous eval₀ := (continuous_apply 1).comp continuous_subtype_val
  obtain ⟨k,hk,ψ,hψ⟩ := continuous_polynomial_recurrence T P eval₀ heval N
  let I : Finset G := insert 1 (P.image (fun p => T.eval (k : ℤ) p))
  let profile : (G → C) → (I → C) := fun f i => f i
  let U := profile ⁻¹' {profile ψ.1}
  have hprofile : Continuous profile := continuous_pi fun i : I => continuous_apply (i : G)
  have hU : IsOpen U := (isOpen_discrete ({profile ψ.1} : Set (I → C))).preimage hprofile
  have hψU : ψ.1 ∈ U := rfl
  obtain ⟨ζ,hζU,hζorb⟩ := mem_closure_iff.mp ψ.2 U hU hψU
  obtain ⟨a,rfl⟩ := hζorb
  refine ⟨k,hk,a,?_⟩
  intro p hp
  have hpI : T.eval (k : ℤ) p ∈ I := Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨p,hp,rfl⟩)
  have hzI : (1 : G) ∈ I := Finset.mem_insert_self _ _
  have hcp := congrFun hζU ⟨T.eval (k : ℤ) p,hpI⟩
  have hcz := congrFun hζU ⟨1,hzI⟩
  change χ (T.eval (k : ℤ) p * a) = ψ.1 (T.eval (k : ℤ) p) at hcp
  change χ (1*a) = ψ.1 1 at hcz
  have hpp := hψ p hp
  change ψ.1 (1 * T.eval (k : ℤ) p) = ψ.1 1 at hpp
  simp only [one_mul] at hpp hcz
  exact hcp.trans (hpp.trans hcz.symm)

end
end GroupPETRecurrence

namespace CubePolynomials
open _root_.OAI.ConstructedWordPlan.CubeFaces
noncomputable section
variable {G : Type*} [Group G]

def evaluation (n : ℤ) : (ℤ → G) →* G where
  toFun f := f n
  map_one' := rfl
  map_mul' _ _ := rfl

def normalized (H : Filtration G) (k : ℕ) : Subgroup (ℤ → G) :=
  polynomials H k ⊓ (evaluation 0).ker

lemma mem_normalized (H : Filtration G) (k : ℕ) (f : ℤ → G) :
    f ∈ normalized H k ↔ f ∈ polynomials H k ∧ f 0 = 1 := Iff.rfl

lemma normalized_antitone (H : Filtration G) : Antitone (normalized H) := by
  intro i j hij f hf
  exact ⟨polynomials_antitone H hij hf.1,hf.2⟩

lemma normalized_normalizes (H : Filtration G) (k : ℕ) :
    normalized H 0 ≤ Subgroup.normalizer (normalized H k) := by
  intro f hf
  rw [mem_normalized] at hf
  apply Subgroup.mem_normalizer_iff.mpr
  intro g
  rw [mem_normalized, mem_normalized]
  constructor
  · intro hg
    refine ⟨(Subgroup.mem_normalizer_iff.mp (normalizes H k hf.1) g).mp hg.1,?_⟩
    change f 0 * g 0 * (f 0)⁻¹ = 1
    rw [hg.2, mul_one, mul_inv_cancel]
  · intro hg
    refine ⟨(Subgroup.mem_normalizer_iff.mp (normalizes H k hf.1) g).mpr hg.1,?_⟩
    have hz := hg.2
    change f 0 * g 0 * (f 0)⁻¹ = 1 at hz
    simpa only [hf.2, one_mul, inv_one, mul_one] using hz

def reversedFiltration (H : Filtration G) (L : ℕ) (hL : H.level L = ⊥) :
    FilteredPET.Filtration (normalized H 0) where
  level d := (normalized H (L-d)).subgroupOf (normalized H 0)
  monotone := by
    intro d e hde f hf
    exact normalized_antitone H (Nat.sub_le_sub_left hde L) hf
  zero := by
    apply le_antisymm _ bot_le
    intro f hf
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    change (f : ℤ → G) ∈ normalized H (L-0) at hf
    rw [mem_normalized, Nat.sub_zero, polynomials_eq_bot hL] at hf
    exact Subgroup.mem_bot.mp hf.1
  exhaustive := by
    intro f
    refine ⟨L,?_⟩
    change (f : ℤ → G) ∈ normalized H (L-L)
    simpa only [Nat.sub_self] using f.2
  normal := by
    intro d
    constructor
    intro f hf g
    have hg := normalized_normalizes H (L-d) g.2
    exact (Subgroup.mem_normalizer_iff.mp hg f).mp hf

def normalizeShift (f : ℤ → G) (t : ℤ) : ℤ → G := fun n => (f t)⁻¹ * f (n+t)

lemma normalizeShift_mem {H : Filtration G} {k : ℕ} {f : ℤ → G}
    (hf : f ∈ normalized H k) (t : ℤ) : normalizeShift f t ∈ normalized H k := by
  rw [mem_normalized] at hf ⊢
  constructor
  · have hc := const_mem ((H.level k).inv_mem (eval_mem hf.1 t))
    exact (polynomials H k).mul_mem hc (shift_mem hf.1 t)
  · change (f t)⁻¹ * f (0+t) = 1
    simp

lemma normalizeShift_lower {H : Filtration G} {k : ℕ} {f : ℤ → G}
    (hf : f ∈ normalized H k) (t : ℤ) :
    normalizeShift f t * f⁻¹ ∈ normalized H (k+1) := by
  rw [mem_normalized] at hf ⊢
  have hd := derivative_mem hf.1 t
  have hv : f t ∈ H.level (k+1) := by
    have hv := eval_mem hd 0
    change (f 0)⁻¹ * f (0+t) ∈ H.level (k+1) at hv
    simpa only [hf.2,inv_one,one_mul,zero_add] using hv
  have hn := (Subgroup.mem_normalizer_iff.mp
    (normalizes H (k+1) (polynomials_antitone H (Nat.zero_le k) hf.1))
    (f⁻¹ * shift t f)).mp hd
  have hc := const_mem ((H.level (k+1)).inv_mem hv)
  have he : normalizeShift f t * f⁻¹ = (fun _ : ℤ => (f t)⁻¹) *
      (f * (f⁻¹ * shift t f) * f⁻¹) := by
    ext n
    change (f t)⁻¹ * f (n+t) * (f n)⁻¹ = (f t)⁻¹ * (f n * ((f n)⁻¹ * f (n+t)) * (f n)⁻¹)
    group
  constructor
  · rw [he]
    exact (polynomials H (k+1)).mul_mem hc hn
  · change ((f t)⁻¹ * f (0+t)) * (f 0)⁻¹ = 1
    simp [hf.2]

def conjugateSequence (g : G) (f : ℤ → G) : ℤ → G := fun n => g⁻¹ * f n * g

lemma conjugateSequence_mem {H : Filtration G} {k : ℕ} {f : ℤ → G}
    (hf : f ∈ normalized H k) {g : G} (hg : g ∈ H.level 0) :
    conjugateSequence g f ∈ normalized H k := by
  rw [mem_normalized] at hf ⊢
  constructor
  · have hc := const_mem ((H.level 0).inv_mem hg)
    have hn := (Subgroup.mem_normalizer_iff.mp (normalizes H k hc) f).mp hf.1
    convert hn using 1
    ext n
    simp [conjugateSequence]
  · simp [conjugateSequence,hf.2]

lemma conjugateSequence_lower {H : Filtration G} {k : ℕ} {f : ℤ → G}
    (hf : f ∈ normalized H k) {g : G} (hg : g ∈ H.level 1) :
    conjugateSequence g f * f⁻¹ ∈ normalized H (k+1) := by
  rw [mem_normalized] at hf ⊢
  constructor
  · have hc := commutator_mem (const_mem ((H.level 1).inv_mem hg)) hf.1
    have he : conjugateSequence g f * f⁻¹ = ⁅(fun _ : ℤ => g⁻¹),f⁆ := by
      ext n
      simp [conjugateSequence,commutatorElement_def]
    rw [he]
    simpa only [Nat.add_comm] using hc
  · simp [conjugateSequence,hf.2]

 

def system (H : Filtration G) (L : ℕ) (htop : H.level 1 = ⊤) (hL : H.level L = ⊥) :
    GroupPET.System G (normalized H 0) where
  filtration := reversedFiltration H L hL
  eval n := (evaluation n).comp (normalized H 0).subtype
  eval_zero f := (mem_normalized H 0 f).mp f.2 |>.2
  shift f t := ⟨normalizeShift f t, normalizeShift_mem f.2 t⟩
  shift_eval f n k := by
    change (f.val n)⁻¹ * f.val (k+n) = (f.val n)⁻¹ * f.val (n+k)
    rw [add_comm k n]
  shift_lower := by
    intro f t
    let F := reversedFiltration H L hL
    change (normalizeShift f t * (f : ℤ → G)⁻¹) ∈ normalized H (L-(F.degree f-1))
    by_cases hf1 : f = 1
    · subst f
      have he : normalizeShift (1 : ℤ → G) t * (1 : ℤ → G)⁻¹ = 1 := by
        ext n
        simp [normalizeShift]
      rw [Subgroup.coe_one,he]
      exact (normalized H _).one_mem
    have hpos : 0 < F.degree f := (F.degree_pos f).mpr hf1
    have hbound : F.degree f ≤ L := (F.degree_le_iff f L).mpr (by
      change (f : ℤ → G) ∈ normalized H (L-L)
      simpa only [Nat.sub_self] using f.2)
    have hmem := F.degree_mem f
    change (f : ℤ → G) ∈ normalized H (L-F.degree f) at hmem
    have he : L-(F.degree f-1) = (L-F.degree f)+1 := by omega
    rw [he]
    exact normalizeShift_lower hmem t
  conjugate g f := ⟨conjugateSequence g f, conjugateSequence_mem f.2
    (H.antitone (Nat.zero_le 1) (by simp [htop]))⟩
  conjugate_eval _ _ _ := rfl
  conjugate_lower := by
    intro g f
    let F := reversedFiltration H L hL
    change conjugateSequence g f * (f : ℤ → G)⁻¹ ∈ normalized H (L-(F.degree f-1))
    by_cases hf1 : f = 1
    · subst f
      have he : conjugateSequence g (1 : ℤ → G) * (1 : ℤ → G)⁻¹ = 1 := by
        ext n
        simp [conjugateSequence]
      rw [Subgroup.coe_one,he]
      exact (normalized H _).one_mem
    have hpos : 0 < F.degree f := (F.degree_pos f).mpr hf1
    have hbound : F.degree f ≤ L := (F.degree_le_iff f L).mpr (by
      change (f : ℤ → G) ∈ normalized H (L-L)
      simpa only [Nat.sub_self] using f.2)
    have hmem := F.degree_mem f
    change (f : ℤ → G) ∈ normalized H (L-F.degree f) at hmem
    have he : L-(F.degree f-1) = (L-F.degree f)+1 := by omega
    rw [he]
    exact conjugateSequence_lower hmem (by simp [htop])

end
end CubePolynomials

 

namespace StretchedFiltration
open Subgroup
variable {G : Type*} [Group G]

 
lemma rotate_le (A B C N : Subgroup G) [N.Normal]
    (h₁ : ⁅⁅B, C⁆, A⁆ ≤ N) (h₂ : ⁅⁅C, A⁆, B⁆ ≤ N) : ⁅⁅A, B⁆, C⁆ ≤ N := by
  let f := QuotientGroup.mk' N
  have hmap (S : Subgroup G) (hS : S ≤ N) : S.map f = ⊥ := by
    apply (Subgroup.map_eq_bot_iff S).mpr
    simpa [f, QuotientGroup.ker_mk'] using hS
  have h₁' : ⁅⁅B.map f, C.map f⁆, A.map f⁆ = ⊥ := by
    simpa only [Subgroup.map_commutator] using hmap _ h₁
  have h₂' : ⁅⁅C.map f, A.map f⁆, B.map f⁆ = ⊥ := by
    simpa only [Subgroup.map_commutator] using hmap _ h₂
  have h : (⁅⁅A, B⁆, C⁆).map f = ⊥ := by
    simpa only [Subgroup.map_commutator] using
      Subgroup.commutator_commutator_eq_bot_of_rotate h₁' h₂'
  have := (Subgroup.map_eq_bot_iff _).mp h
  simpa [f, QuotientGroup.ker_mk'] using this

 
theorem lower_bracket (a b : ℕ) :
    ⁅(⊤ : Subgroup G).lowerCentralSeries a, (⊤ : Subgroup G).lowerCentralSeries b⁆ ≤
      (⊤ : Subgroup G).lowerCentralSeries (a + b + 1) := by
  induction a generalizing b with
  | zero =>
    rw [Subgroup.lowerCentralSeries_zero, Subgroup.commutator_comm,
      ← Subgroup.lowerCentralSeries_succ]
    simp
  | succ a ih =>
    rw [Subgroup.lowerCentralSeries_succ]
    apply rotate_le
    · rw [Subgroup.commutator_comm (⊤ : Subgroup G),
        ← Subgroup.lowerCentralSeries_succ, Subgroup.commutator_comm]
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (b + 1)
    · have h := Subgroup.commutator_mono
        (show ⁅(⊤ : Subgroup G).lowerCentralSeries b,
            (⊤ : Subgroup G).lowerCentralSeries a⁆ ≤
            (⊤ : Subgroup G).lowerCentralSeries (a + b + 1) from by
          rw [Subgroup.commutator_comm]
          exact ih b) (le_refl (⊤ : Subgroup G))
      simpa only [← Subgroup.lowerCentralSeries_succ,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

 

def stretch (D : ℕ) (i : ℕ) : Subgroup G :=
  (⊤ : Subgroup G).lowerCentralSeries ((i - 1) / D)

lemma stretch_antitone (D : ℕ) : Antitone (stretch (G := G) D) := by
  intro i j hij
  exact (⊤ : Subgroup G).lowerCentralSeries_antitone (Nat.div_le_div_right (Nat.sub_le_sub_right hij 1))

@[simp] lemma stretch_zero (D : ℕ) : stretch (G := G) D 0 = ⊤ := by
  simp [stretch]

@[simp] lemma stretch_one (D : ℕ) : stretch (G := G) D 1 = ⊤ := by
  simp [stretch]

lemma stretch_eq_top {D i : ℕ} (hD : 0 < D) (hi : i ≤ D) :
    stretch (G := G) D i = ⊤ := by
  have : i - 1 < D := by omega
  simp [stretch, Nat.div_eq_of_lt this]

lemma stretch_terminal {D s : ℕ} (hD : 0 < D)
    (hs : (⊤ : Subgroup G).lowerCentralSeries s = ⊥) :
    stretch (G := G) D (s * D + 1) = ⊥ := by
  simpa [stretch, Nat.mul_div_cancel, Nat.ne_of_gt hD] using hs

lemma stretch_bracket {D : ℕ} (hD : 0 < D) (i j : ℕ) :
    ⁅stretch (G := G) D i, stretch (G := G) D j⁆ ≤ stretch (G := G) D (i + j) := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp only [Nat.zero_add, stretch_zero]
    unfold stretch
    exact Subgroup.commutator_le_right _ _
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp only [Nat.add_zero, stretch_zero]
    unfold stretch
    exact Subgroup.commutator_le_left _ _
  apply (lower_bracket ((i - 1) / D) ((j - 1) / D)).trans
  apply (⊤ : Subgroup G).lowerCentralSeries_antitone
  have h₁ := Nat.mod_lt (i - 1) hD
  have h₂ := Nat.mod_lt (j - 1) hD
  have h₃ := Nat.div_add_mod (i - 1) D
  have h₄ := Nat.div_add_mod (j - 1) D
  have h₅ := Nat.div_add_mod (i + j - 1) D
  have h₆ := Nat.mod_lt (i + j - 1) hD
  by_contra h
  have hh : ((i - 1) / D + (j - 1) / D + 2) * D ≤ (i + j - 1) / D * D :=
    Nat.mul_le_mul_right D (by omega)
  have hsum : i + j - 1 = (i - 1) + (j - 1) + 1 := by omega
  have hh' : D * ((i - 1) / D) + D * ((j - 1) / D) + 2 * D ≤
      D * ((i + j - 1) / D) := by nlinarith only [hh]
  omega

end StretchedFiltration

namespace NilpotentPolynomialRecurrence
open _root_.Polynomial _root_.OAI.Polynomial
noncomputable section
variable {G : Type*} [Group G]

 
def word (w : List (G × ℤ[X])) (k : ℤ) : G :=
  (w.map (fun ap => ap.1 ^ ap.2.eval k)).prod

lemma word_mem (H : CubeFaces.Filtration G) (D : ℕ) (hD : H.level D = ⊤)
    (w : List (G × ℤ[X]))
    (hw : ∀ ap ∈ w, ap.2.eval 0 = 0 ∧ ap.2.natDegree ≤ D) :
    word w ∈ CubePolynomials.normalized H 0 := by
  rw [CubePolynomials.mem_normalized]
  induction w with
  | nil =>
    constructor
    · exact (CubePolynomials.polynomials H 0).one_mem
    · simp [word]
  | cons ap w ih =>
    have hap := hw ap (List.mem_cons_self ..)
    have hwt := ih (fun bp hbp => hw bp (List.mem_cons_of_mem _ hbp))
    have ha := CubePolynomials.power_polynomial_mem D 0 ap.1
      (show ap.1 ∈ H.level (D+0) from by simp [hD]) ap.2 hap.2
    constructor
    · exact (CubePolynomials.polynomials H 0).mul_mem ha hwt.1
    · simp only [word,List.map_cons,List.prod_cons, hap.1,zpow_zero,one_mul]
      exact hwt.2

 

theorem coloring_recurrence [Group.IsNilpotent G] {C : Type*} [Fintype C]
    (W : Finset (List (G × ℤ[X])))
    (hW : ∀ w ∈ W, ∀ ap ∈ w, ap.2.eval 0 = 0)
    (χ : G → C) (N : ℕ) :
    ∃ k : ℕ, N < k ∧ ∃ J : G, ∀ w ∈ W, χ (word w k * J) = χ J := by
  classical
  let D : ℕ := W.sup (fun w => (w.map (fun ap => ap.2.natDegree)).foldr max 0) + 1
  have hD : 0 < D := Nat.zero_lt_succ _
  let H : CubeFaces.Filtration G := {
    level := StretchedFiltration.stretch D
    antitone := StretchedFiltration.stretch_antitone D
    commutator_le := StretchedFiltration.stretch_bracket hD }
  obtain ⟨s,hs⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp (inferInstance : Group.IsNilpotent G)
  let L := s*D+1
  have htop : H.level 1 = ⊤ := StretchedFiltration.stretch_one D
  have hL : H.level L = ⊥ := StretchedFiltration.stretch_terminal hD hs
  let T := CubePolynomials.system H L htop hL
  have hmem : ∀ w ∈ W, word w ∈ CubePolynomials.normalized H 0 := by
    intro w hw
    apply word_mem H D (StretchedFiltration.stretch_eq_top hD le_rfl) w
    intro ap hap
    refine ⟨hW w hw ap hap,?_⟩
    have hm : ap.2.natDegree ≤ (w.map (fun ap => ap.2.natDegree)).foldr max 0 := by
      clear hw
      induction w with
      | nil => simp at hap
      | cons bp w ih =>
        simp only [List.mem_cons] at hap
        simp only [List.map_cons,List.foldr_cons]
        rcases hap with rfl | hap
        · exact le_max_left _ _
        · exact (ih hap).trans (le_max_right _ _)
    apply hm.trans
    calc
      _ ≤ W.sup (fun v => (v.map (fun ap => ap.2.natDegree)).foldr max 0) := Finset.le_sup hw
      _ ≤ D := Nat.le_succ _
  let lift : W → CubePolynomials.normalized H 0 := fun w => ⟨word w.1, hmem w.1 w.2⟩
  let P := Finset.univ.image lift
  let : TopologicalSpace C := ⊥
  let : DiscreteTopology C := ⟨rfl⟩
  obtain ⟨k,hk,J,hJ⟩ := GroupPETRecurrence.coloring_polynomial_recurrence T P χ N
  refine ⟨k,hk,J,?_⟩
  intro w hw
  exact hJ (lift ⟨w,hw⟩) (Finset.mem_image.mpr ⟨⟨w,hw⟩,Finset.mem_univ _,rfl⟩)

end
end NilpotentPolynomialRecurrence

 

namespace UniformRecurrence

variable {G : Type*} [Group G] {κ : Type*} [Fintype κ]

 
def Recurs {ι : Type*} (w : ι → ℕ → G) (χ : G → κ) : Prop :=
  ∃ k : ℕ, 0 < k ∧ ∃ J : G, ∀ i, χ (w i k * J) = χ J

 

theorem finite_alternatives {ι : Type*} [Fintype ι] (w : ι → ℕ → G)
    (h : ∀ χ : G → κ, Recurs w χ) :
    ∃ O : Finset (ℕ × G), (∀ o ∈ O, 0 < o.1) ∧
      ∀ χ : G → κ, ∃ o ∈ O, ∀ i, χ (w i o.1 * o.2) = χ o.2 := by
  classical
  let : TopologicalSpace κ := ⊥
  let : DiscreteTopology κ := ⟨rfl⟩
  let U : (ℕ+ × G) → Set (G → κ) := fun o =>
    {χ | ∀ i, χ (w i o.1 * o.2) = χ o.2}
  have hopen (o) : IsOpen (U o) := by
    unfold U
    simp only [Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro i
    change IsOpen ((fun χ : G → κ => (χ (w i o.1 * o.2), χ o.2)) ⁻¹'
      {p : κ × κ | p.1 = p.2})
    exact (isOpen_discrete {p : κ × κ | p.1 = p.2}).preimage
      ((continuous_apply (w i o.1 * o.2)).prodMk (continuous_apply o.2))
  have hcover : (Set.univ : Set (G → κ)) ⊆ ⋃ o, U o := by
    intro χ _
    obtain ⟨k, hk, J, hJ⟩ := h χ
    exact Set.mem_iUnion.mpr ⟨(⟨k, hk⟩, J), hJ⟩
  obtain ⟨O, hO⟩ := isCompact_univ.elim_finite_subcover U hopen hcover
  refine ⟨O.image (fun o => (o.1.val, o.2)), ?_, ?_⟩
  · intro o ho
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp ho
    exact p.1.pos
  · intro χ
    have hχ := hO (Set.mem_univ χ)
    obtain ⟨o, ho, hχ⟩ := Set.mem_iUnion₂.mp hχ
    exact ⟨(o.1.val, o.2), Finset.mem_image.mpr ⟨o, ho, rfl⟩, hχ⟩

 
structure PolynomialWord (A : Type*) where
  letters : List (A × Polynomial ℤ)
  vanishes : ∀ u ∈ letters, u.2.eval 0 = 0

namespace PolynomialWord
variable {A H : Type*} [Group H]
def eval (p : PolynomialWord A) (a : A → H) (k : ℕ) : H :=
  (p.letters.map (fun u => a u.1 ^ u.2.eval (k : ℤ))).prod

lemma map_eval (p : PolynomialWord A) (a : A → G) (f : G →* H) (k : ℕ) :
    f (p.eval a k) = p.eval (f ∘ a) k := by
  simp [eval, map_list_prod, List.map_map, Function.comp_def]

lemma eval_zero (p : PolynomialWord A) (a : A → G) : p.eval a 0 = 1 := by
  unfold eval
  apply List.prod_eq_one
  intro x hx
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx
  simp [p.vanishes u hu]
end PolynomialWord

 

def FreeNilpotent (A : Type*) (s : ℕ) :=
  FreeGroup A ⧸ (⊤ : Subgroup (FreeGroup A)).lowerCentralSeries s

instance {A : Type*} {s : ℕ} : Group (FreeNilpotent A s) := by
  unfold FreeNilpotent
  infer_instance

namespace FreeNilpotent
variable {A : Type*} {s : ℕ}

def of (a : A) : FreeNilpotent A s :=
  QuotientGroup.mk (FreeGroup.of a)

 
theorem lower_eq_bot :
    (⊤ : Subgroup (FreeNilpotent A s)).lowerCentralSeries s = ⊥ := by
  let N := (⊤ : Subgroup (FreeGroup A)).lowerCentralSeries s
  let f : FreeGroup A →* FreeNilpotent A s := QuotientGroup.mk' N
  have htop : (⊤ : Subgroup (FreeGroup A)).map f = ⊤ :=
    f.range_eq_map.symm.trans (MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N))
  have hmap : N.map f = ⊥ := (Subgroup.map_eq_bot_iff _).mpr (by
    change N ≤ (QuotientGroup.mk' N).ker
    rw [QuotientGroup.ker_mk'])
  rw [← htop, ← Subgroup.map_lowerCentralSeries]
  exact hmap

instance : Group.IsNilpotent (FreeNilpotent A s) :=
  Subgroup.nilpotent_iff_lowerCentralSeries.mpr ⟨s, lower_eq_bot⟩

instance [Countable A] : Countable (FreeNilpotent A s) := by
  have : Countable (FreeGroup A) := by
    unfold FreeGroup
    infer_instance
  exact (QuotientGroup.mk'_surjective
    ((⊤ : Subgroup (FreeGroup A)).lowerCentralSeries s)).countable

private theorem lift_kernel (a : A → G)
    (hG : (⊤ : Subgroup G).lowerCentralSeries s = ⊥) :
    (⊤ : Subgroup (FreeGroup A)).lowerCentralSeries s ≤ (FreeGroup.lift a).ker := by
  apply (Subgroup.map_eq_bot_iff _).mp
  rw [Subgroup.map_lowerCentralSeries]
  apply le_bot_iff.mp
  calc
    ((⊤ : Subgroup (FreeGroup A)).map (FreeGroup.lift a)).lowerCentralSeries s
        ≤ (⊤ : Subgroup G).lowerCentralSeries s := Subgroup.lowerCentralSeries_mono s le_top
    _ = ⊥ := hG

 
noncomputable def lift (a : A → G)
    (hG : (⊤ : Subgroup G).lowerCentralSeries s = ⊥) : FreeNilpotent A s →* G :=
  QuotientGroup.lift _ (FreeGroup.lift a) (lift_kernel a hG)

@[simp] theorem lift_of (a : A → G)
    (hG : (⊤ : Subgroup G).lowerCentralSeries s = ⊥) (x : A) :
    lift a hG (of x) = a x := by
  change FreeGroup.lift a (FreeGroup.of x) = a x
  exact FreeGroup.lift_apply_of

lemma lift_polynomialWord (p : PolynomialWord A) (a : A → G)
    (hG : (⊤ : Subgroup G).lowerCentralSeries s = ⊥) (k : ℕ) :
    lift a hG (p.eval (of (s := s)) k) = p.eval a k := by
  rw [PolynomialWord.map_eval]
  congr 1
  funext x
  exact lift_of a hG x

end FreeNilpotent

end UniformRecurrence

namespace UniformRecurrence
noncomputable section
variable {A ι κ : Type*} [Fintype ι] [Fintype κ]

 

theorem universal_quotient_alternatives (s : ℕ) (p : ι → PolynomialWord A) :
    ∃ O : Finset (ℕ × FreeNilpotent A s), (∀ o ∈ O, 0 < o.1) ∧
      ∀ χ : FreeNilpotent A s → κ, ∃ o ∈ O, ∀ i,
        χ ((p i).eval FreeNilpotent.of o.1 * o.2) = χ o.2 := by
  classical
  apply finite_alternatives
  intro χ
  let letters (i : ι) : List (FreeNilpotent A s × Polynomial ℤ) :=
    (p i).letters.map (fun ap => (FreeNilpotent.of ap.1, ap.2))
  let W := Finset.univ.image letters
  have hW : ∀ w ∈ W, ∀ ap ∈ w, ap.2.eval 0 = 0 := by
    intro w hw ap hap
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨bp, hbp, rfl⟩ := List.mem_map.mp hap
    exact (p i).vanishes bp hbp
  obtain ⟨k, hk, J, hJ⟩ :=
    NilpotentPolynomialRecurrence.coloring_recurrence W hW χ 0
  refine ⟨k, hk, J, ?_⟩
  intro i
  have hi := hJ (letters i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  simpa only [NilpotentPolynomialRecurrence.word, letters, List.map_map,
    Function.comp_def, PolynomialWord.eval] using hi

 

theorem universal_finite_alternatives (s : ℕ) (p : ι → PolynomialWord A) :
    ∃ O : Finset (ℕ × FreeGroup A), (∀ o ∈ O, 0 < o.1) ∧
      ∀ (G : Type*) [Group G]
        (_hG : (⊤ : Subgroup G).lowerCentralSeries s = ⊥)
        (a : A → G) (χ : G → κ), ∃ o ∈ O, ∀ i,
        χ ((p i).eval a o.1 * FreeGroup.lift a o.2) = χ (FreeGroup.lift a o.2) := by
  classical
  obtain ⟨O, hpos, hO⟩ := universal_quotient_alternatives (κ := κ) s p
  let N := (⊤ : Subgroup (FreeGroup A)).lowerCentralSeries s
  let q : FreeGroup A →* FreeNilpotent A s := QuotientGroup.mk' N
  let rep : FreeNilpotent A s → FreeGroup A := fun g =>
    Classical.choose (QuotientGroup.mk'_surjective N g)
  have hrep (g : FreeNilpotent A s) : q (rep g) = g :=
    Classical.choose_spec (QuotientGroup.mk'_surjective N g)
  refine ⟨O.image (fun o => (o.1, rep o.2)), ?_, ?_⟩
  · intro o ho
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ho
    exact hpos u hu
  · intro G _ hG a χ
    let f := FreeNilpotent.lift a hG
    obtain ⟨o, ho, heq⟩ := hO (χ ∘ f)
    refine ⟨(o.1,rep o.2), Finset.mem_image.mpr ⟨o, ho, rfl⟩, ?_⟩
    intro i
    have hf : f o.2 = FreeGroup.lift a (rep o.2) := by
      calc
        f o.2 = f (q (rep o.2)) := congrArg f (hrep o.2).symm
        _ = FreeGroup.lift a (rep o.2) := rfl
    have hi := heq i
    change χ (f ((p i).eval FreeNilpotent.of o.1 * o.2)) = χ (f o.2) at hi
    rw [map_mul, FreeNilpotent.lift_polynomialWord, hf] at hi
    exact hi

end
end UniformRecurrence

namespace FiniteWordPlan
open UniformRecurrence
noncomputable section
variable {A G X Label κ : Type*} [Group G] [MulAction G X]

 

def inflate (lam : A → ℕ) (k : ℕ) : FreeGroup A →* FreeGroup A :=
  FreeGroup.lift (fun a => FreeGroup.of a ^ (k ^ lam a))

def polynomial (lam : A → ℕ) (hlam : ∀ a, 0 < lam a) (w : FreeGroup A) :
    PolynomialWord A := by
  classical
  exact {
    letters := w.toWord.map (fun u =>
      (u.1, if u.2 then (Polynomial.X : Polynomial ℤ) ^ lam u.1 else -Polynomial.X ^ lam u.1))
    vanishes := by
      intro u hu
      obtain ⟨v, _, rfl⟩ := List.mem_map.mp hu
      cases v.2 <;> simp [Nat.ne_of_gt (hlam v.1)] }

lemma eval_polynomial (lam : A → ℕ) (hlam : ∀ a, 0 < lam a)
    (w : FreeGroup A) (a : A → G) (k : ℕ) :
    (polynomial lam hlam w).eval a k = FreeGroup.lift a (inflate lam k w) := by
  classical
  conv_rhs => rw [← FreeGroup.mk_toWord (x := w)]
  simp only [inflate, FreeGroup.lift_mk, map_list_prod, List.map_map,
    Function.comp_def]
  unfold PolynomialWord.eval polynomial
  simp only [List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro u _
  cases u.2 <;> simp
  all_goals rw [← Int.natCast_pow, zpow_natCast]

lemma interpretation_inflation (lam : A → ℕ) (k : ℕ) (a a' : A → G)
    (h : ∀ u, a' u = a u ^ (k ^ lam u)) (w : FreeGroup A) :
    FreeGroup.lift a' w = FreeGroup.lift a (inflate lam k w) := by
  have hh : FreeGroup.lift a' = (FreeGroup.lift a).comp (inflate lam k) := by
    apply FreeGroup.ext_hom
    intro u
    simpa [inflate] using h u
  exact DFunLike.congr_fun hh w

 

theorem update_options [Fintype κ] (s : ℕ) (lam : A → ℕ) (hlam : ∀ a, 0 < lam a)
    (W : Finset (FreeGroup A)) :
    ∃ O : Finset (ℕ × FreeGroup A), (∀ o ∈ O, 0 < o.1) ∧
      ∀ (G : Type*) [Group G]
        (_hG : (⊤ : Subgroup G).lowerCentralSeries s = ⊥)
        (X : Type*) [MulAction G X] (a : A → G) (C : X → κ) (x : X),
        ∃ o ∈ O, ∀ w ∈ W,
          C (FreeGroup.lift a (inflate lam o.1 w) • (FreeGroup.lift a o.2 • x)) =
            C (FreeGroup.lift a o.2 • x) := by
  classical
  obtain ⟨O,hpos,hO⟩ := universal_finite_alternatives (κ := κ) s
    (fun w : W => polynomial lam hlam w.1)
  refine ⟨O,hpos,?_⟩
  intro G _ hG X _ a C x
  obtain ⟨o,ho,heq⟩ := hO G hG a (fun g => C (g • x))
  refine ⟨o,ho,?_⟩
  intro w hw
  have hh := heq ⟨w,hw⟩
  simpa only [eval_polynomial, mul_smul] using hh

 
def Requirement (C : Label → X → κ) (a : A → G)
    (R : Finset (Label × FreeGroup A)) (x : X) : Prop :=
  ∀ r ∈ R, C r.1 x = C r.1 (FreeGroup.lift a r.2 • x)

 

def predecessor [DecidableEq Label] [DecidableEq A]
    (lam : A → ℕ) (f : ℕ → Label → Label)
    (O : Finset (ℕ × FreeGroup A)) (R : Finset (Label × FreeGroup A)) :
    Finset (Label × FreeGroup A) :=
  O.biUnion (fun o => R.biUnion (fun r =>
    {(f o.1 r.1,o.2), (f o.1 r.1, inflate lam o.1 r.2 * o.2)}))

 

lemma protect_jump [DecidableEq Label] [DecidableEq A]
    (lam : A → ℕ) (f : ℕ → Label → Label)
    (O : Finset (ℕ × FreeGroup A)) (R : Finset (Label × FreeGroup A))
    (C C' : Label → X → κ) (a a' : A → G) (x : X)
    (o : ℕ × FreeGroup A) (ho : o ∈ O)
    (hC : ∀ l, C' l = C (f o.1 l))
    (ha : ∀ u, a' u = a u ^ (o.1 ^ lam u))
    (h : Requirement C a (predecessor lam f O R) x) :
    Requirement C' a' R (FreeGroup.lift a o.2 • x) := by
  intro r hr
  have hmem₁ : (f o.1 r.1,o.2) ∈ predecessor lam f O R := by
    apply Finset.mem_biUnion.mpr ⟨o,ho,?_⟩
    exact Finset.mem_biUnion.mpr ⟨r,hr,by simp⟩
  have hmem₂ : (f o.1 r.1,inflate lam o.1 r.2 * o.2) ∈ predecessor lam f O R := by
    apply Finset.mem_biUnion.mpr ⟨o,ho,?_⟩
    exact Finset.mem_biUnion.mpr ⟨r,hr,by simp⟩
  have h₁ := h _ hmem₁
  have h₂ := h _ hmem₂
  dsimp only at h₁ h₂
  rw [hC, interpretation_inflation lam o.1 a a' ha,
    ← mul_smul, ← map_mul]
  exact h₁.symm.trans h₂

end
end FiniteWordPlan

namespace FiniteWordPlan
noncomputable section

 

structure ScaleSystem (A Label G X S κ : Type*) [Group G] [MulAction G X]
    (lam : ℕ → A → ℕ) (f : ℕ → ℕ → Label → Label) where
  update : ℕ → ℕ → S → S
  letter : S → A → G
  color : S → Label → X → κ
  letter_update : ∀ n k st, 0 < k → ∀ a,
    letter (update n k st) a = letter st a ^ (k ^ lam n a)
  color_update : ∀ n k st, 0 < k → ∀ l,
    color (update n k st) l = color st (f n k l)

variable {A Label G X S κ : Type*} [Group G] [MulAction G X]
    {lam : ℕ → A → ℕ} {f : ℕ → ℕ → Label → Label}

 

def run (T : ScaleSystem A Label G X S κ lam f) :
    ℕ → List (ℕ × FreeGroup A) → S → X → S × X
  | _, [], st, x => (st, x)
  | n, o :: p, st, x => run T (n + 1) p (T.update n o.1 st)
      (FreeGroup.lift (T.letter st) o.2 • x)

lemma run_append (T : ScaleSystem A Label G X S κ lam f)
    (p q : List (ℕ × FreeGroup A)) (n : ℕ) (st : S) (x : X) :
    run T n (p ++ q) st x =
      run T (n + p.length) q (run T n p st x).1 (run T n p st x).2 := by
  induction p generalizing n st x with
  | nil => simp [run]
  | cons o p ih =>
    simp only [List.cons_append, run, List.length_cons]
    rw [ih]
    congr 1; omega

 

theorem pivot_plan [Fintype κ] (s : ℕ) (lam : ℕ → A → ℕ)
    (hlam : ∀ n a, 0 < lam n a) (f : ℕ → ℕ → Label → Label)
    (tag : Label → ℕ) (htag : ∀ n k l, tag (f n k l) = tag l)
    (hfix : ∀ n k l, tag l = n → f n k l = l)
    (q : ℕ) (R : Finset (Label × FreeGroup A))
    (hR : ∀ r ∈ R, tag r.1 < q) :
    ∃ P : Finset (List (ℕ × FreeGroup A)),
      (∀ p ∈ P, p.length = q ∧ ∀ o ∈ p, 0 < o.1) ∧
      ∀ (G : Type*) [Group G]
        (_hG : (⊤ : Subgroup G).lowerCentralSeries s = ⊥)
        (X : Type*) [MulAction G X] (S : Type*)
        (T : ScaleSystem A Label G X S κ lam f) (st : S) (x : X),
        ∃ p ∈ P, Requirement (T.color (run T 0 p st x).1)
          (T.letter (run T 0 p st x).1) R (run T 0 p st x).2 := by
  classical
  induction q generalizing R with
  | zero =>
    refine ⟨{[]}, ?_, ?_⟩
    · intro p hp
      simp only [Finset.mem_singleton] at hp
      subst p
      simp
    · intro G _ _ X _ S T st x
      refine ⟨[], by simp, ?_⟩
      intro r hr
      exact False.elim (Nat.not_lt_zero _ (hR r hr))
  | succ n ih =>
    let Rold := R.filter (fun r => tag r.1 < n)
    let Rnew := R.filter (fun r => tag r.1 = n)
    let L := Rnew.image Prod.fst
    let W := Rnew.image Prod.snd
    obtain ⟨O, hpos, hO⟩ := update_options (κ := L → κ) s (lam n) (hlam n) W
    let Rpre := predecessor (lam n) (f n) O Rold
    have hpre : ∀ r ∈ Rpre, tag r.1 < n := by
      intro r hr
      obtain ⟨o, _, ho⟩ := Finset.mem_biUnion.mp hr
      obtain ⟨v, hv, hrv⟩ := Finset.mem_biUnion.mp ho
      have hvtag := (Finset.mem_filter.mp hv).2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hrv
      rcases hrv with rfl | rfl <;> simpa only [htag] using hvtag
    obtain ⟨P, hP, hrun⟩ := ih Rpre hpre
    refine ⟨P.biUnion (fun p => O.image (fun o => p ++ [o])), ?_, ?_⟩
    · intro p hp
      obtain ⟨v, hv, hp⟩ := Finset.mem_biUnion.mp hp
      obtain ⟨o, ho, rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨hlen, hpositive⟩ := hP v hv
      constructor
      · simp [hlen]
      · intro u hu
        rcases List.mem_append.mp hu with hu | hu
        · exact hpositive u hu
        · have he : u = o := List.mem_singleton.mp hu
          simpa only [he] using hpos o ho
    · intro G _ hG X _ S T st x
      obtain ⟨p, hp, hprev⟩ := hrun G hG X S T st x
      let stp := (run T 0 p st x).1
      let xp := (run T 0 p st x).2
      let C : X → L → κ := fun y l => T.color stp l.1 y
      obtain ⟨o, ho, hrec⟩ := hO G hG X (T.letter stp) C xp
      have hlen := (hP p hp).1
      have hrunlast : run T 0 (p ++ [o]) st x =
          (T.update n o.1 stp, FreeGroup.lift (T.letter stp) o.2 • xp) := by
        rw [run_append, hlen, Nat.zero_add]
        rfl
      refine ⟨p ++ [o], Finset.mem_biUnion.mpr ⟨p,hp,Finset.mem_image.mpr ⟨o,ho,rfl⟩⟩, ?_⟩
      rw [hrunlast]
      have hold : Requirement (T.color (T.update n o.1 stp))
          (T.letter (T.update n o.1 stp)) Rold
          (FreeGroup.lift (T.letter stp) o.2 • xp) :=
        protect_jump (lam n) (f n) O Rold (T.color stp)
          (T.color (T.update n o.1 stp)) (T.letter stp)
          (T.letter (T.update n o.1 stp)) xp o ho
          (T.color_update n o.1 stp (hpos o ho))
          (T.letter_update n o.1 stp (hpos o ho)) hprev
      intro r hr
      by_cases ht : tag r.1 < n
      · exact hold r (Finset.mem_filter.mpr ⟨hr,ht⟩)
      · have htagr : tag r.1 = n := by have := hR r hr; omega
        have hrnew : r ∈ Rnew := Finset.mem_filter.mpr ⟨hr,htagr⟩
        have hl : r.1 ∈ L := Finset.mem_image.mpr ⟨r,hrnew,rfl⟩
        have hw : r.2 ∈ W := Finset.mem_image.mpr ⟨r,hrnew,rfl⟩
        have hh := congrFun (hrec r.2 hw) ⟨r.1,hl⟩
        dsimp only [C] at hh
        change T.color (T.update n o.1 stp) r.1 _ =
          T.color (T.update n o.1 stp) r.1 _
        rw [T.color_update n o.1 stp (hpos o ho), hfix n o.1 r.1 htagr,
          interpretation_inflation (lam n) o.1 (T.letter stp)
            (T.letter (T.update n o.1 stp))
            (T.letter_update n o.1 stp (hpos o ho))]
        exact hh.symm

end
end FiniteWordPlan

 

namespace AlignmentScales
open scoped BigOperators

def weight {n : ℕ} (i : Fin n) : ℕ := 2 ^ (n - (i.val + 1))
def weightSum {n : ℕ} (A : Finset (Fin n)) : ℕ := ∑ i ∈ A, weight i

lemma geom_sum (k : ℕ) : (∑ j ∈ Finset.range k, 2 ^ j) + 1 = 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, pow_succ]; omega

 
lemma sum_later_lt {n : ℕ} (a : Fin n) (C : Finset (Fin n))
    (hC : ∀ c ∈ C, a < c) : weightSum C < weight a := by
  classical
  let e : Fin n → ℕ := fun i => n - (i.val + 1)
  have hinj : Function.Injective e := by
    intro i j h
    apply Fin.ext
    dsimp [e] at h
    have := i.isLt
    have := j.isLt
    omega
  have hsub : C.image e ⊆ Finset.range (e a) := by
    intro j hj
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hj
    have hlt := hC c hc
    change a.val < c.val at hlt
    apply Finset.mem_range.mpr
    dsimp [e]
    have := c.isLt
    omega
  have hs : weightSum C ≤ ∑ j ∈ Finset.range (e a), 2 ^ j := by
    calc
      weightSum C = ∑ j ∈ C.image e, 2 ^ j := by
        rw [Finset.sum_image (fun i _ j _ h => hinj h)]
        rfl
      _ ≤ _ := Finset.sum_le_sum_of_subset hsub
  have hh := geom_sum (e a)
  change weightSum C < 2 ^ e a
  omega

lemma weightSum_nonneg {n : ℕ} (A : Finset (Fin n)) : 0 ≤ (weightSum A : ℤ) :=
  Int.natCast_nonneg _

 

lemma exponent_pos {n : ℕ} (A C T : Finset (Fin n))
    (hAC : ∃ a ∈ A, ∀ c ∈ C, a < c) :
    0 < (weightSum A : ℤ) - weightSum C + weightSum T := by
  obtain ⟨a,ha,hC⟩ := hAC
  have h₁ := sum_later_lt a C hC
  have h₂ : weight a ≤ weightSum A := Finset.single_le_sum (fun i _ => Nat.zero_le _ ) ha
  have h₃ := weightSum_nonneg T
  omega

 
def updateExponent {n : ℕ} (i : Fin n) (T : Finset (Fin n)) (l : Fin n) : ℤ :=
  if l < i then weight l else if l = i then -(weightSum T : ℤ) else 0

 
def multiplier {n : ℕ} (i : Fin n) (T : Finset (Fin n)) (k : ℚ) (l : Fin n) : ℚ :=
  k ^ updateExponent i T l

def blockProduct {n : ℕ} (b : Fin n → ℚ) (A : Finset (Fin n)) : ℚ := ∏ l ∈ A, b l

def update {n : ℕ} (b : Fin n → ℚ) (i : Fin n) (T : Finset (Fin n)) (k : ℚ) : Fin n → ℚ :=
  fun l => b l * multiplier i T k l

lemma multiplier_pos {n : ℕ} (i : Fin n) (T : Finset (Fin n)) {k : ℚ}
    (hk : 0 < k) (l : Fin n) : 0 < multiplier i T k l := zpow_pos hk _

lemma blockProduct_update {n : ℕ} (b : Fin n → ℚ) (i : Fin n) (T A : Finset (Fin n))
    (k : ℚ) :
    blockProduct (update b i T k) A = blockProduct b A * blockProduct (multiplier i T k) A := by
  exact Finset.prod_mul_distrib

lemma blockProduct_multiplier {n : ℕ} (i : Fin n) (T A : Finset (Fin n))
    {k : ℚ} (hk : k ≠ 0) :
    blockProduct (multiplier i T k) A = k ^ (∑ l ∈ A, updateExponent i T l) := by
  classical
  induction A using Finset.induction_on with
  | empty => simp [blockProduct]
  | @insert a A ha ih =>
    simp only [blockProduct, Finset.prod_insert ha, Finset.sum_insert ha] at *
    rw [ih, zpow_add₀ hk]
    rfl

lemma exponentSum_before {n : ℕ} (i : Fin n) (T A : Finset (Fin n))
    (hA : ∀ l ∈ A, l < i) :
    (∑ l ∈ A, updateExponent i T l) = (weightSum A : ℤ) := by
  simp only [weightSum, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro l hl
  simp [updateExponent, hA l hl]

lemma exponentSum_target {n : ℕ} (i : Fin n) (T C : Finset (Fin n))
    (hC : ∀ l ∈ C, l < i) :
    (∑ l ∈ insert i C, updateExponent i T l) = (weightSum C : ℤ) - weightSum T := by
  classical
  have hi : i ∉ C := fun h => (lt_irrefl i) (hC i h)
  rw [Finset.sum_insert hi, exponentSum_before i T C hC]
  simp [updateExponent]
  ring

 
lemma target_preserved {n : ℕ} (b : Fin n → ℚ) (i : Fin n) (T : Finset (Fin n))
    (hT : ∀ l ∈ T, l < i) {k : ℚ} (hk : k ≠ 0) :
    blockProduct (update b i T k) (insert i T) = blockProduct b (insert i T) := by
  rw [blockProduct_update, blockProduct_multiplier i T _ hk,
    exponentSum_target i T T hT, sub_self, zpow_zero, mul_one]

 
lemma ratio_update {n : ℕ} (b : Fin n → ℚ) (i : Fin n) (T A C : Finset (Fin n))
    (hA : ∀ l ∈ A, l < i) (hC : ∀ l ∈ C, l < i) {k : ℚ} (hk : k ≠ 0) :
    blockProduct (update b i T k) A / blockProduct (update b i T k) (insert i C) =
      (blockProduct b A / blockProduct b (insert i C)) *
        k ^ ((weightSum A : ℤ) - weightSum C + weightSum T) := by
  rw [blockProduct_update, blockProduct_update,
    blockProduct_multiplier i T A hk, blockProduct_multiplier i T (insert i C) hk,
    exponentSum_before i T A hA, exponentSum_target i T C hC]
  rw [mul_div_mul_comm, ← zpow_sub₀ hk]
  congr 2
  ring

end AlignmentScales

 

namespace RationalPivotPlan
open AlignmentScales
noncomputable section

variable {n q : ℕ} (i : Fin n) (tail : Fin q → Finset (Fin n))

def tailAt (j : ℕ) : Finset (Fin n) := if h : j < q then tail ⟨j,h⟩ else ∅

lemma tailAt_fin (j : Fin q) : tailAt tail j.val = tail j := by
  simp [tailAt]

def block (j : Fin q) : Finset (Fin n) := insert i (tail j)

def transport (j k : ℕ) (l : Fin q × ℚ) : Fin q × ℚ :=
  (l.1, l.2 * blockProduct (multiplier i (tailAt tail j) (k : ℚ)) (block i tail l.1))

lemma transport_tag (j k : ℕ) (l : Fin q × ℚ) :
    (transport i tail j k l).1.val = l.1.val := rfl

 

def transportPos (j k : ℕ) (l : Fin q × ℚ) : Fin q × ℚ :=
  if k = 0 then l else transport i tail j k l

lemma transportPos_tag (j k : ℕ) (l : Fin q × ℚ) :
    (transportPos i tail j k l).1.val = l.1.val := by
  simp only [transportPos]
  split <;> rfl

lemma transportPos_fix (htail : ∀ j a, a ∈ tail j → a < i)
    (j k : ℕ) (l : Fin q × ℚ) (h : l.1.val = j) :
    transportPos i tail j k l = l := by
  classical
  by_cases hk : k = 0
  · simp [transportPos, hk]
  · simp only [transportPos, ite_eq_right hk, transport]
    apply Prod.ext
    · rfl
    dsimp
    rw [← h, tailAt_fin, block, blockProduct_multiplier _ _ _ (by exact_mod_cast hk),
      exponentSum_target i (tail l.1) (tail l.1) (htail l.1), sub_self, zpow_zero,
      mul_one]

variable {E : Type*} (owner : E → Fin q) (added : E → Finset (Fin n))

def exponent (j : ℕ) (e : E) : ℤ :=
  (weightSum (added e) : ℤ) - weightSum (tail (owner e)) + weightSum (tailAt tail j)

def lam (j : ℕ) (e : E × ℚ) : ℕ := (exponent tail owner added j e.1).toNat

lemma exponent_positive
    (hbefore : ∀ e, ∃ a ∈ added e, ∀ c ∈ tail (owner e), a < c) (j : ℕ) (e : E) :
    0 < exponent tail owner added j e :=
  exponent_pos _ _ _ (hbefore e)

lemma lam_positive
    (hbefore : ∀ e, ∃ a ∈ added e, ∀ c ∈ tail (owner e), a < c) (j : ℕ) (e : E × ℚ) :
    0 < lam tail owner added j e := by
  have h := exponent_positive tail owner added hbefore j e.1
  dsimp [lam]
  omega

variable {G X κ : Type*} [Group G] [MulAction G X]

 
abbrev State := (Fin n → ℚ) × (E × ℚ → G)

def system (C : Fin q → ℚ → X → κ) :
    FiniteWordPlan.ScaleSystem (E × ℚ) (Fin q × ℚ) G X
      (State (n := n) (E := E) (G := G)) κ
      (lam tail owner added) (transportPos i tail) where
  update j k st := (update st.1 i (tailAt tail j) k,
    fun e => st.2 e ^ (k ^ lam tail owner added j e))
  letter st := st.2
  color st l := C l.1 (l.2 * blockProduct st.1 (block i tail l.1))
  letter_update _ _ _ _ _ := rfl
  color_update j k st hk l := by
    simp only [transportPos, ite_eq_right (Nat.ne_of_gt hk), transport]
    rw [blockProduct_update]
    congr 1
    ring

 

theorem rational_pivot_plan [Fintype κ] (s : ℕ)
    (htail : ∀ j a, a ∈ tail j → a < i)
    (hbefore : ∀ e, ∃ a ∈ added e, ∀ c ∈ tail (owner e), a < c)
    (R : Finset ((Fin q × ℚ) × FreeGroup (E × ℚ))) :
    ∃ P : Finset (List (ℕ × FreeGroup (E × ℚ))),
      (∀ p ∈ P, p.length = q ∧ ∀ o ∈ p, 0 < o.1) ∧
      ∀ (G : Type*) [Group G]
        (_hG : (⊤ : Subgroup G).lowerCentralSeries s = ⊥)
        (X : Type*) [MulAction G X] (C : Fin q → ℚ → X → κ)
        (b : Fin n → ℚ) (a : E × ℚ → G) (x : X),
        ∃ p ∈ P, let z := FiniteWordPlan.run (system i tail owner added C) 0 p (b,a) x
          FiniteWordPlan.Requirement
            (fun l => C l.1 (l.2 * blockProduct z.1.1 (block i tail l.1)))
            z.1.2 R z.2 := by
  obtain ⟨P,hP,h⟩ := FiniteWordPlan.pivot_plan (κ := κ) s (lam tail owner added)
    (lam_positive tail owner added hbefore) (transportPos i tail) (fun l => l.1.val)
    (transportPos_tag i tail) (transportPos_fix i tail htail) q R
    (fun r _ => r.1.1.isLt)
  refine ⟨P,hP,?_⟩
  intro G _ hG X _ C b a x
  exact h G hG X _ (system i tail owner added C) (b,a) x

end
end RationalPivotPlan

namespace RationalPivotPlan
open AlignmentScales
noncomputable section
variable {n q : ℕ} {E G X κ : Type*} [Group G] [MulAction G X]
    (i : Fin n) (tail : Fin q → Finset (Fin n))
    (owner : E → Fin q) (added : E → Finset (Fin n))

def qExponent (q₀ : ℕ) (b : Fin n → ℚ) (e : E × ℚ) : ℚ :=
  q₀ * e.2 * (blockProduct b (added e.1) / blockProduct b (block i tail (owner e.1)))

lemma qExponent_update
    (htail : ∀ j a, a ∈ tail j → a < i)
    (hadded : ∀ e a, a ∈ added e → a < i)
    (hbefore : ∀ e, ∃ a ∈ added e, ∀ c ∈ tail (owner e), a < c)
    (q₀ : ℕ) (b : Fin n → ℚ) (j k : ℕ) (hk : 0 < k) (e : E × ℚ) :
    qExponent i tail owner added q₀ (update b i (tailAt tail j) k) e =
      qExponent i tail owner added q₀ b e * (k ^ lam tail owner added j e : ℕ) := by
  unfold qExponent
  rw [block, ratio_update b i (tailAt tail j) (added e.1) (tail (owner e.1))
    (hadded e.1) (htail (owner e.1)) (by exact_mod_cast Nat.ne_of_gt hk)]
  have hh : (lam tail owner added j e : ℤ) = exponent tail owner added j e.1 :=
    Int.toNat_of_nonneg (le_of_lt (exponent_positive tail owner added hbefore j e.1))
  change (q₀ : ℚ) * e.2 *
    (_ * (k : ℚ) ^ exponent tail owner added j e.1) = _
  rw [← hh, zpow_natCast, Nat.cast_pow]
  ring

 

def Realizes (L : E → G) (q₀ : ℕ) (K : Finset (E × ℚ))
    (b : Fin n → ℚ) (a : E × ℚ → G) : Prop :=
  ∀ e ∈ K, ∃ m : ℤ, qExponent i tail owner added q₀ b e = m ∧ a e = L e.1 ^ m

lemma realizes_update
    (htail : ∀ j a, a ∈ tail j → a < i)
    (hadded : ∀ e a, a ∈ added e → a < i)
    (hbefore : ∀ e, ∃ a ∈ added e, ∀ c ∈ tail (owner e), a < c)
    (L : E → G) (q₀ : ℕ) (K : Finset (E × ℚ)) (b : Fin n → ℚ) (a : E × ℚ → G)
    (h : Realizes i tail owner added L q₀ K b a) (j k : ℕ) (hk : 0 < k) :
    Realizes i tail owner added L q₀ K (update b i (tailAt tail j) k)
      (fun e => a e ^ (k ^ lam tail owner added j e)) := by
  intro e he
  obtain ⟨m,hm,ha⟩ := h e he
  refine ⟨m * (k ^ lam tail owner added j e : ℕ), ?_, ?_⟩
  · rw [qExponent_update i tail owner added htail hadded hbefore q₀ b j k hk e, hm]
    push_cast
    rfl
  · dsimp only
    rw [ha, zpow_mul, zpow_natCast]

lemma realizes_run
    (htail : ∀ j a, a ∈ tail j → a < i)
    (hadded : ∀ e a, a ∈ added e → a < i)
    (hbefore : ∀ e, ∃ a ∈ added e, ∀ c ∈ tail (owner e), a < c)
    (L : E → G) (q₀ : ℕ) (K : Finset (E × ℚ)) (C : Fin q → ℚ → X → κ)
    (p : List (ℕ × FreeGroup (E × ℚ))) (hp : ∀ o ∈ p, 0 < o.1)
    (j : ℕ) (b : Fin n → ℚ) (a : E × ℚ → G) (x : X)
    (h : Realizes i tail owner added L q₀ K b a) :
    let z := FiniteWordPlan.run (system i tail owner added C) j p (b,a) x
    Realizes i tail owner added L q₀ K z.1.1 z.1.2 := by
  induction p generalizing j b a x with
  | nil => exact h
  | cons o p ih =>
    apply ih (fun v hv => hp v (List.mem_cons_of_mem o hv))
    exact realizes_update i tail owner added htail hadded hbefore L q₀ K b a h j o.1
      (hp o (List.mem_cons_self))

def letters {A : Type*} (w : FreeGroup A) : Finset A := by
  classical
  exact (w.toWord.map Prod.fst).toFinset

lemma lift_congr_on_letters {A : Type*} (a b : A → G) (w : FreeGroup A)
    (h : ∀ t ∈ letters w, a t = b t) : FreeGroup.lift a w = FreeGroup.lift b w := by
  classical
  conv_lhs => rw [← FreeGroup.mk_toWord (x := w), FreeGroup.lift_mk]
  conv_rhs => rw [← FreeGroup.mk_toWord (x := w), FreeGroup.lift_mk]
  congr 1
  apply List.map_congr_left
  intro u hu
  have hu' : u.1 ∈ letters w := by
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨u,hu,rfl⟩)
  rw [h u.1 hu']

 

def letter (L : E → G) (q₀ : ℕ) (b : Fin n → ℚ) (e : E × ℚ) : G :=
  L e.1 ^ (qExponent i tail owner added q₀ b e).num

lemma realizes_lift (L : E → G) (q₀ : ℕ) (K : Finset (E × ℚ))
    (b : Fin n → ℚ) (a : E × ℚ → G) (h : Realizes i tail owner added L q₀ K b a)
    (w : FreeGroup (E × ℚ)) (hw : letters w ⊆ K) :
    FreeGroup.lift a w = FreeGroup.lift (letter i tail owner added L q₀ b) w := by
  apply lift_congr_on_letters
  intro e he
  obtain ⟨m,hm,ha⟩ := h e (hw he)
  simpa [letter,hm] using ha

 
theorem finite_denominator {A : Type*} (K : Finset A) (v : A → ℚ) :
    ∃ q₀ : ℕ, 0 < q₀ ∧ ∀ a ∈ K, ∃ m : ℤ, (q₀ : ℚ) * v a = m := by
  classical
  let q₀ := ∏ a ∈ K, (v a).den
  refine ⟨q₀, Finset.prod_pos (fun a _ => (v a).den_pos), ?_⟩
  intro a ha
  have hd : (v a).den ∣ q₀ := Finset.dvd_prod_of_mem (fun a => (v a).den) ha
  obtain ⟨d,hd⟩ := hd
  refine ⟨(d : ℤ) * (v a).num, ?_⟩
  rw [hd]
  push_cast
  calc
    (v a).den * (d : ℚ) * v a = d * ((v a).den * v a) := by ring
    _ = _ := by
      congr 1
      calc
        ((v a).den : ℚ) * v a = (v a).den * ((v a).num / (v a).den) := by rw [Rat.num_div_den]
        _ = (v a).num := mul_div_cancel₀ _ (by exact_mod_cast (v a).den_ne_zero)

end
end RationalPivotPlan

namespace RationalPivotPlan
open AlignmentScales
noncomputable section
variable {n q : ℕ} {E G X κ : Type*} [Group G] [MulAction G X]
    (i : Fin n) (tail : Fin q → Finset (Fin n))
    (owner : E → Fin q) (added : E → Finset (Fin n))

 

def exactRun (L : E → G) (q₀ : ℕ) :
    ℕ → List (ℕ × FreeGroup (E × ℚ)) → (Fin n → ℚ) → X → (Fin n → ℚ) × X
  | _, [], b, x => (b,x)
  | j, o :: p, b, x => exactRun L q₀ (j+1) p (update b i (tailAt tail j) o.1)
      (FreeGroup.lift (letter i tail owner added L q₀ b) o.2 • x)

lemma run_eq_exact
    (htail : ∀ j a, a ∈ tail j → a < i)
    (hadded : ∀ e a, a ∈ added e → a < i)
    (hbefore : ∀ e, ∃ a ∈ added e, ∀ c ∈ tail (owner e), a < c)
    (L : E → G) (q₀ : ℕ) (K : Finset (E × ℚ)) (C : Fin q → ℚ → X → κ)
    (p : List (ℕ × FreeGroup (E × ℚ)))
    (hp : ∀ o ∈ p, 0 < o.1 ∧ letters o.2 ⊆ K)
    (j : ℕ) (b : Fin n → ℚ) (a : E × ℚ → G) (x : X)
    (h : Realizes i tail owner added L q₀ K b a) :
    let z := FiniteWordPlan.run (system i tail owner added C) j p (b,a) x
    (z.1.1,z.2) = exactRun i tail owner added L q₀ j p b x := by
  induction p generalizing j b a x with
  | nil => rfl
  | cons o p ih =>
    have ho := hp o List.mem_cons_self
    have hpre := realizes_update i tail owner added htail hadded hbefore L q₀ K b a h j o.1 ho.1
    simp only [FiniteWordPlan.run, exactRun]
    change _ = exactRun i tail owner added L q₀ (j+1) p _ _
    calc
      _ = exactRun i tail owner added L q₀ (j+1) p _ (FreeGroup.lift a o.2 • x) :=
        ih (fun v hv => hp v (List.mem_cons_of_mem o hv)) _ _ _ _ hpre
      _ = _ := by rw [realizes_lift i tail owner added L q₀ K b a h o.2 ho.2]

lemma realizes_letter (L : E → G) (q₀ : ℕ) (K : Finset (E × ℚ)) (b : Fin n → ℚ)
    (h : ∀ e ∈ K, ∃ m : ℤ, qExponent i tail owner added q₀ b e = m) :
    Realizes i tail owner added L q₀ K b (letter i tail owner added L q₀ b) := by
  intro e he
  obtain ⟨m,hm⟩ := h e he
  exact ⟨m,hm, by simp [letter,hm]⟩

 

theorem integral_pivot_plan [Fintype κ] (s : ℕ)
    (htail : ∀ j a, a ∈ tail j → a < i)
    (hadded : ∀ e a, a ∈ added e → a < i)
    (hbefore : ∀ e, ∃ a ∈ added e, ∀ c ∈ tail (owner e), a < c)
    (R : Finset ((Fin q × ℚ) × FreeGroup (E × ℚ))) :
    ∃ P : Finset (List (ℕ × FreeGroup (E × ℚ))),
      (∀ p ∈ P, p.length = q ∧ ∀ o ∈ p, 0 < o.1) ∧
      ∀ B : Finset (Fin n → ℚ), ∃ Q : ℕ, 0 < Q ∧
      ∀ q₀ : ℕ, Q ∣ q₀ → ∀ (G : Type*) [Group G]
        (_hG : (⊤ : Subgroup G).lowerCentralSeries s = ⊥)
        (X : Type*) [MulAction G X] (C : Fin q → ℚ → X → κ)
        (L : E → G) (b : Fin n → ℚ) (_hb : b ∈ B) (x : X),
      ∃ p ∈ P, let z := exactRun i tail owner added L q₀ 0 p b x
        FiniteWordPlan.Requirement
          (fun l => C l.1 (l.2 * blockProduct z.1 (block i tail l.1)))
          (letter i tail owner added L q₀ z.1) R z.2 := by
  classical
  obtain ⟨P,hP,hrec⟩ := rational_pivot_plan (κ := κ) i tail owner added s htail hbefore R
  refine ⟨P,hP,?_⟩
  intro B
  let K := (R.biUnion (fun r => letters r.2)) ∪
    P.biUnion (fun p => p.toFinset.biUnion (fun o => letters o.2))
  obtain ⟨Q,hQ,hclear⟩ := finite_denominator (B ×ˢ K)
    (fun z => z.2.2 * (blockProduct z.1 (added z.2.1) /
      blockProduct z.1 (block i tail (owner z.2.1))))
  refine ⟨Q,hQ,?_⟩
  intro q₀ hq₀ G _ hG X _ C L b hb x
  obtain ⟨d,hd⟩ := hq₀
  have hreal := realizes_letter i tail owner added L q₀ K b (by
    intro e he
    obtain ⟨m,hm⟩ := hclear (b,e) (Finset.mem_product.mpr ⟨hb,he⟩)
    refine ⟨(d : ℤ) * m,?_⟩
    dsimp only [qExponent]
    rw [hd]
    push_cast
    calc
      (Q : ℚ) * d * e.2 * (blockProduct b (added e.1) /
        blockProduct b (block i tail (owner e.1))) =
        d * ((Q : ℚ) * (e.2 * (blockProduct b (added e.1) /
          blockProduct b (block i tail (owner e.1))))) := by ring
      _ = _ := by rw [hm])
  obtain ⟨p,hp,hgood⟩ := hrec G hG X C b (letter i tail owner added L q₀ b) x
  have hp' : ∀ o ∈ p, 0 < o.1 ∧ letters o.2 ⊆ K := by
    intro o ho
    refine ⟨(hP p hp).2 o ho, ?_⟩
    intro e he
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨p,hp,
      Finset.mem_biUnion.mpr ⟨o,List.mem_toFinset.mpr ho,he⟩⟩)
  have heq := run_eq_exact i tail owner added htail hadded hbefore L q₀ K C p hp' 0 b
    (letter i tail owner added L q₀ b) x hreal
  have hrun := realizes_run i tail owner added htail hadded hbefore L q₀ K C p
    (fun o ho => (hp' o ho).1) 0 b (letter i tail owner added L q₀ b) x hreal
  refine ⟨p,hp,?_⟩
  rw [← heq]
  dsimp only
  intro r hr
  have hw : letters r.2 ⊆ K := fun _ he =>
    Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨r,hr,he⟩)
  have hg := hgood r hr
  rw [realizes_lift i tail owner added L q₀ K _ _ hrun r.2 hw] at hg
  exact hg

end
end RationalPivotPlan

 

namespace GlobalWordPlan
open AlignmentScales RationalPivotPlan
noncomputable section

structure Pivot (n : ℕ) where
  index : Fin n
  targets : ℕ
  tail : Fin targets → Finset (Fin n)
  pairs : ℕ
  owner : Fin pairs → Fin targets
  added : Fin pairs → Finset (Fin n)
  tail_lt : ∀ j a, a ∈ tail j → a < index
  added_lt : ∀ e a, a ∈ added e → a < index
  before : ∀ e, ∃ a ∈ added e, ∀ c ∈ tail (owner e), a < c

variable {n : ℕ}
abbrev Scale (n : ℕ) := Fin n → ℚ
abbrev Alphabet (D : Pivot n) := Fin D.pairs × ℚ
abbrev Path (D : Pivot n) := List (ℕ × FreeGroup (Alphabet D))

def scaleRun (D : Pivot n) : ℕ → Path D → Scale n → Scale n
  | _, [], b => b
  | j, o :: p, b => scaleRun D (j+1) p (update b D.index (tailAt D.tail j) o.1)

lemma update_mul (b d : Scale n) (i : Fin n) (T : Finset (Fin n)) (k : ℚ) :
    update (b*d) i T k = b * update d i T k := by
  funext l
  simp only [update, Pi.mul_apply]
  ring

lemma scaleRun_mul (D : Pivot n) (p : Path D) (j : ℕ) (b d : Scale n) :
    scaleRun D j p (b*d) = b * scaleRun D j p d := by
  induction p generalizing j d with
  | nil => rfl
  | cons o p ih => simp only [scaleRun,update_mul,ih]

lemma scaleRun_eq_mul (D : Pivot n) (p : Path D) (j : ℕ) (b : Scale n) :
    scaleRun D j p b = b * scaleRun D j p 1 := by
  simpa only [mul_one] using scaleRun_mul D p j b 1

lemma exactRun_fst (D : Pivot n) {G X : Type*} [Group G] [MulAction G X]
    (L : Fin D.pairs → G) (q₀ j : ℕ) (p : Path D) (b : Scale n) (x : X) :
    (exactRun D.index D.tail D.owner D.added L q₀ j p b x).1 = scaleRun D j p b := by
  induction p generalizing j b x with
  | nil => rfl
  | cons o p ih => exact ih _ _ _

lemma blockProduct_mul (b d : Scale n) (A : Finset (Fin n)) :
    blockProduct (b*d) A = blockProduct b A * blockProduct d A := by
  simp only [blockProduct,Pi.mul_apply,Finset.prod_mul_distrib]

def adjust (D : Pivot n) (d : Scale n) (e : Alphabet D) : Alphabet D :=
  (e.1,e.2 * (blockProduct d (D.added e.1) /
    blockProduct d (block D.index D.tail (D.owner e.1))))

lemma qExponent_adjust (D : Pivot n) (d b : Scale n) (q₀ : ℕ) (e : Alphabet D) :
    qExponent D.index D.tail D.owner D.added q₀ b (adjust D d e) =
      qExponent D.index D.tail D.owner D.added q₀ (b*d) e := by
  simp only [qExponent,adjust,blockProduct_mul]
  rw [mul_div_mul_comm]
  ring

lemma lift_adjust (D : Pivot n) (d b : Scale n) (q₀ : ℕ)
    {G : Type*} [Group G] (L : Fin D.pairs → G) (w : FreeGroup (Alphabet D)) :
    FreeGroup.lift (letter D.index D.tail D.owner D.added L q₀ b)
      (FreeGroup.map (adjust D d) w) =
    FreeGroup.lift (letter D.index D.tail D.owner D.added L q₀ (b*d)) w := by
  have hh : (FreeGroup.lift (letter D.index D.tail D.owner D.added L q₀ b)).comp
      (FreeGroup.map (adjust D d)) =
      FreeGroup.lift (letter D.index D.tail D.owner D.added L q₀ (b*d)) := by
    apply FreeGroup.ext_hom
    intro e
    simp only [MonoidHom.comp_apply,FreeGroup.map.of,FreeGroup.lift_apply_of,letter,
      qExponent_adjust]
    rfl
  exact DFunLike.congr_fun hh w

 

def baseWord (D : Pivot n) (U : Finset (Fin D.pairs)) : FreeGroup (Alphabet D) :=
  (U.toList.map (fun e => FreeGroup.of (e,(1:ℚ)))).prod

def terminal (D : Pivot n) (F : Finset (Scale n)) :
    Finset ((Fin D.targets × ℚ) × FreeGroup (Alphabet D)) :=
  F.biUnion (fun d => Finset.univ.biUnion (fun j : Fin D.targets =>
    ((Finset.univ.filter (fun e => D.owner e = j)).powerset).image
      (fun U => ((j,blockProduct d (block D.index D.tail j)),
        FreeGroup.map (adjust D d) (baseWord D U)))))

def Good (D : Pivot n) {G X κ : Type*} [Group G] [MulAction G X]
    (C : Fin D.targets → ℚ → X → κ) (L : Fin D.pairs → G)
    (q₀ : ℕ) (b : Scale n) (x : X) : Prop :=
  ∀ (j : Fin D.targets) (U : Finset (Fin D.pairs)), (∀ e ∈ U, D.owner e = j) →
    C j (blockProduct b (block D.index D.tail j)) x =
      C j (blockProduct b (block D.index D.tail j))
        (FreeGroup.lift (letter D.index D.tail D.owner D.added L q₀ b) (baseWord D U) • x)

lemma good_future (D : Pivot n) (F : Finset (Scale n))
    {G X κ : Type*} [Group G] [MulAction G X]
    (C : Fin D.targets → ℚ → X → κ) (L : Fin D.pairs → G)
    (q₀ : ℕ) (b : Scale n) (x : X)
    (h : FiniteWordPlan.Requirement
      (fun l => C l.1 (l.2 * blockProduct b (block D.index D.tail l.1)))
      (letter D.index D.tail D.owner D.added L q₀ b) (terminal D F) x)
    (d : Scale n) (hd : d ∈ F) : Good D C L q₀ (b*d) x := by
  intro j U hU
  have hmem : ((j,blockProduct d (block D.index D.tail j)),
      FreeGroup.map (adjust D d) (baseWord D U)) ∈ terminal D F := by
    apply Finset.mem_biUnion.mpr ⟨d,hd,?_⟩
    apply Finset.mem_biUnion.mpr ⟨j,Finset.mem_univ j,?_⟩
    apply Finset.mem_image.mpr ⟨U,?_,rfl⟩
    exact Finset.mem_powerset.mpr (fun e he => Finset.mem_filter.mpr ⟨Finset.mem_univ e,hU e he⟩)
  have hh := h _ hmem
  dsimp only at hh
  rw [lift_adjust] at hh
  simpa only [blockProduct_mul,mul_comm] using hh

 
theorem pivot_future_plan {κ : Type*} [Fintype κ] (s : ℕ) (D : Pivot n)
    (F : Finset (Scale n)) :
    ∃ P : Finset (Path D),
      (∀ p ∈ P, p.length = D.targets ∧ ∀ o ∈ p, 0 < o.1) ∧
      ∀ B : Finset (Scale n), ∃ Q : ℕ, 0 < Q ∧
      ∀ q₀ : ℕ, Q ∣ q₀ → ∀ (G : Type*) [Group G]
        (_hG : (⊤ : Subgroup G).lowerCentralSeries s = ⊥)
        (X : Type*) [MulAction G X] (C : Fin D.targets → ℚ → X → κ)
        (L : Fin D.pairs → G) (b : Scale n) (_hb : b ∈ B) (x : X),
      ∃ p ∈ P, ∀ d ∈ F,
        Good D C L q₀ (scaleRun D 0 p b * d)
          (exactRun D.index D.tail D.owner D.added L q₀ 0 p b x).2 := by
  obtain ⟨P,hP,h⟩ := integral_pivot_plan (κ := κ) D.index D.tail D.owner D.added s
    D.tail_lt D.added_lt D.before (terminal D F)
  refine ⟨P,hP,?_⟩
  intro B
  obtain ⟨Q,hQ,h⟩ := h B
  refine ⟨Q,hQ,?_⟩
  intro q₀ hq₀ G _ hG X _ C L b hb x
  obtain ⟨p,hp,h⟩ := h q₀ hq₀ G hG X C L b hb x
  refine ⟨p,hp,?_⟩
  intro d hd
  have hg := good_future D F C L q₀ _ _ h d hd
  simpa only [exactRun_fst] using hg

end
end GlobalWordPlan

namespace GlobalWordPlan
open AlignmentScales RationalPivotPlan
noncomputable section
universe u w
variable {n : ℕ} {κ : Type w}

 
def Plan : List (Pivot n) → Type
  | [] => Unit
  | D :: Ds => Finset (Path D) × Plan Ds

def ChoicePath : List (Pivot n) → Type
  | [] => Unit
  | D :: Ds => Path D × ChoicePath Ds

def Admitted : {Ds : List (Pivot n)} → Plan Ds → ChoicePath Ds → Prop
  | [], _, _ => True
  | _ :: _, P, p => p.1 ∈ P.1 ∧ Admitted P.2 p.2

def positivePlan : {Ds : List (Pivot n)} → Plan Ds → Prop
  | [], _ => True
  | D :: _, P => (∀ p ∈ P.1, p.length = D.targets ∧ ∀ o ∈ p, 0 < o.1) ∧ positivePlan P.2

def pathMultiplier : {Ds : List (Pivot n)} → ChoicePath Ds → Scale n
  | [], _ => 1
  | D :: _, p => scaleRun D 0 p.1 1 * pathMultiplier p.2

def multipliers : {Ds : List (Pivot n)} → Plan Ds → Finset (Scale n)
  | [], _ => {1}
  | D :: _, P => P.1.biUnion (fun p => (multipliers P.2).image
      (fun d => scaleRun D 0 p 1 * d))

lemma pathMultiplier_mem : {Ds : List (Pivot n)} → (P : Plan Ds) → (p : ChoicePath Ds) →
    Admitted P p → pathMultiplier p ∈ multipliers P
  | [], _, _, _ => Finset.mem_singleton.mpr rfl
  | _ :: _, P, p, h => Finset.mem_biUnion.mpr ⟨p.1,h.1,
      Finset.mem_image.mpr ⟨pathMultiplier p.2,pathMultiplier_mem P.2 p.2 h.2,rfl⟩⟩

 

structure Action (s : ℕ) (κ : Type w) (D : Pivot n) where
  G : Type u
  group : Group G
  nilpotent : (⊤ : Subgroup G).lowerCentralSeries s = ⊥
  X : Type u
  action : MulAction G X
  palette : Fin D.targets → ℚ → X → κ
  generators : Fin D.pairs → G

attribute [instance] Action.group Action.action

def Actions (s : ℕ) (κ : Type w) : List (Pivot n) → Type (max (u+1) w)
  | [] => ULift.{max (u+1) w} Unit
  | D :: Ds => Action.{u,w} s κ D × Actions s κ Ds

def States {s : ℕ} : {Ds : List (Pivot n)} → Actions.{u,w} s κ Ds → Type (max (u+1) w)
  | [], _ => ULift.{max (u+1) w} Unit
  | _ :: _, A => A.1.X × States A.2

 
def execute {s : ℕ} : {Ds : List (Pivot n)} → (A : Actions.{u,w} s κ Ds) →
    ℕ → ChoicePath Ds → Scale n → States A → Scale n × States A
  | [], _, _, _, b, x => (b,x)
  | D :: _, A, q₀, p, b, x =>
      let z := exactRun D.index D.tail D.owner D.added A.1.generators q₀ 0 p.1 b x.1
      let y := execute A.2 q₀ p.2 z.1 x.2
      (y.1,(z.2,y.2))

def allGood {s : ℕ} : {Ds : List (Pivot n)} → (A : Actions.{u,w} s κ Ds) →
    ℕ → Scale n → States A → Prop
  | [], _, _, _, _ => True
  | D :: _, A, q₀, b, x =>
      Good D A.1.palette A.1.generators q₀ b x.1 ∧ allGood A.2 q₀ b x.2

lemma execute_fst {s : ℕ} : {Ds : List (Pivot n)} → (A : Actions.{u,w} s κ Ds) →
    (q₀ : ℕ) → (p : ChoicePath Ds) → (b : Scale n) → (x : States A) →
    (execute A q₀ p b x).1 = b * pathMultiplier p
  | [], _, _, _, _, _ => (mul_one _).symm
  | D :: _, A, q₀, p, b, x => by
      change (execute A.2 q₀ p.2 _ x.2).1 = _
      rw [execute_fst A.2,exactRun_fst,scaleRun_eq_mul]
      exact mul_assoc _ _ _

 

theorem finite_word_plan [Fintype κ] (s : ℕ) (Ds : List (Pivot n)) :
    ∃ P : Plan Ds, positivePlan P ∧
      ∀ B : Finset (Scale n), ∃ Q : ℕ, 0 < Q ∧
      ∀ q₀ : ℕ, Q ∣ q₀ → ∀ (A : Actions.{u,w} s κ Ds)
        (b : Scale n) (_hb : b ∈ B) (x : States A),
        ∃ p : ChoicePath Ds, Admitted P p ∧
          allGood A q₀ (execute A q₀ p b x).1 (execute A q₀ p b x).2 := by
  classical
  induction Ds with
  | nil =>
    refine ⟨(),True.intro,?_⟩
    intro B
    refine ⟨1,by decide,?_⟩
    intro q₀ _ A b _ x
    exact ⟨(),True.intro,True.intro⟩
  | cons D Ds ih =>
    obtain ⟨Ptail,hposTail,hTail⟩ := ih
    obtain ⟨Phead,hposHead,hHead⟩ := pivot_future_plan (κ := κ) s D (multipliers Ptail)
    refine ⟨(Phead,Ptail),⟨hposHead,hposTail⟩,?_⟩
    intro B
    let Bnext := B.biUnion (fun b => Phead.image (fun p => scaleRun D 0 p b))
    obtain ⟨Qhead,hQhead,hHead⟩ := hHead B
    obtain ⟨Qtail,hQtail,hTail⟩ := hTail Bnext
    refine ⟨Qhead * Qtail,Nat.mul_pos hQhead hQtail,?_⟩
    intro q₀ hq₀ A b hb x
    have hdivHead : Qhead ∣ q₀ := dvd_trans (dvd_mul_right Qhead Qtail) hq₀
    have hdivTail : Qtail ∣ q₀ := dvd_trans (dvd_mul_left Qtail Qhead) hq₀
    obtain ⟨phead,hphead,hgoodHead⟩ := hHead q₀ hdivHead A.1.G A.1.nilpotent
      A.1.X A.1.palette A.1.generators b hb x.1
    let z := exactRun D.index D.tail D.owner D.added A.1.generators q₀ 0 phead b x.1
    have hz : z.1 ∈ Bnext := by
      rw [exactRun_fst]
      exact Finset.mem_biUnion.mpr ⟨b,hb,Finset.mem_image.mpr ⟨phead,hphead,rfl⟩⟩
    obtain ⟨ptail,hptail,hgoodTail⟩ := hTail q₀ hdivTail A.2 z.1 hz x.2
    refine ⟨(phead,ptail),⟨hphead,hptail⟩,?_,hgoodTail⟩
    have hg := hgoodHead (pathMultiplier ptail) (pathMultiplier_mem Ptail ptail hptail)
    change Good D A.1.palette A.1.generators q₀
      (execute A.2 q₀ ptail z.1 x.2).1 z.2
    rw [execute_fst,exactRun_fst]
    exact hg

end
end GlobalWordPlan

end ConstructedWordPlan
 

end
end

end OAI
