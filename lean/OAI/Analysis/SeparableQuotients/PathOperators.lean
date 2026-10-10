import OAI.Analysis.SeparableQuotients.LpDuality

namespace OAI

noncomputable section

namespace SeparableQuotient.Norming
open scoped ENNReal

def Family.pathExponent (f : Family) : ℝ≥0∞ := ENNReal.ofReal f.q
lemma Family.q_gt_one (f : Family) : 1 < f.q := (Parameters.q_bounds f.s_ge_two).1
lemma Family.q_pos (f : Family) : 0 < f.q := zero_lt_one.trans f.q_gt_one
instance Family.pathExponent_fact (f : Family) : Fact (1 ≤ f.pathExponent) :=
  ⟨by simpa [Family.pathExponent] using ENNReal.ofReal_le_ofReal f.q_gt_one.le⟩
@[simp] lemma Family.pathExponent_real (f : Family) : f.pathExponent.toReal = f.q :=
  ENNReal.toReal_ofReal f.q_pos.le
lemma Family.pathExponent_pos (f : Family) : 0 < f.pathExponent.toReal := by simpa using f.q_pos
lemma Family.pathExponent_ne_top (f : Family) : f.pathExponent ≠ ∞ := ENNReal.ofReal_ne_top
end SeparableQuotient.Norming

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding Filter
open scoped Classical Topology
@[reducible] local instance pathDualGroup : NormedAddCommGroup (StrongDual ℝ E) := inferInstance
@[reducible] local instance pathDualSpace : NormedSpace ℝ (StrongDual ℝ E) := inferInstance
abbrev W := (StrongDual ℝ E) ⧸ X₀
@[reducible] local instance wGroup : NormedAddCommGroup W := inferInstance
@[reducible] local instance wSpace : NormedSpace ℝ W := inferInstance
local instance wComplete : CompleteSpace W := inferInstance

def pathCoset {f : Family} (P : PathIndex f) : W := X₀.mkQL (pathFunctional P.repr)

lemma coset_sum_bound {f : Family} {h : ℕ} (P : Fin h → PathIndex f)
    (hinj : Function.Injective P) (c : Fin h → ℝ) :
    ‖∑ i, c i • pathCoset (P i)‖ ≤ (∑ i, |c i|^f.q)^(1/f.q) := by
  obtain ⟨N,hN⟩ := exists_tail_estimate (fun i => (P i).repr)
    (PathIndex.repr_injective.comp hinj)
  have he (i : Fin h) : pathCoset (P i) = X₀.mkQL (pathTail (P i).repr N) := by
    apply (Submodule.Quotient.eq X₀).mpr
    exact pathTail_complement_mem _ _
  simp_rw [he]
  simp_rw [← map_smul]
  rw [← map_sum]
  exact (Submodule.Quotient.norm_mk_le _ _).trans (hN c)

def finitePathMap (f : Family) : (PathIndex f →₀ ℝ) →ₗ[ℝ] W :=
  Finsupp.linearCombination ℝ pathCoset

lemma finitePathMap_bound (f : Family) (c : PathIndex f →₀ ℝ) :
    ‖finitePathMap f c‖ ≤ ‖LpCoding.finite f.pathExponent c‖ := by
  let e : Fin c.support.card ≃ c.support := c.support.equivFin.symm
  have h := coset_sum_bound (fun i => (e i).val)
    (Subtype.val_injective.comp e.injective) (fun i => c (e i))
  have he : finitePathMap f c = ∑ i : Fin c.support.card, c (e i) • pathCoset (e i).val := by
    change (∑ a ∈ c.support, c a • pathCoset a) = _
    rw [← Finset.sum_attach]
    exact (e.sum_comp (fun a : c.support => c a • pathCoset a.val)).symm
  have hs : (∑ a ∈ c.support, |c a|^f.q) = ∑ i, |c (e i)|^f.q := by
    rw [← Finset.sum_attach]
    exact (e.sum_comp (fun a : c.support => |c a|^f.q)).symm
  rw [he,LpCoding.norm_finite f.pathExponent_pos,Family.pathExponent_real,hs]
  exact h

/-- A bounded path map constructed by completion of path cosets. -/
def pathMap (f : Family) : lp (fun _ : PathIndex f => ℝ) f.pathExponent →L[ℝ] W :=
  (finitePathMap f).extendOfNorm (LpCoding.finite f.pathExponent)

lemma norm_pathMap_le (f : Family) : ‖pathMap f‖ ≤ 1 := by
  exact LinearMap.opNorm_extendOfNorm_le (f := finitePathMap f)
    (e := LpCoding.finite f.pathExponent)
    (LpCoding.finite_dense (ι := PathIndex f) (p := f.pathExponent) f.pathExponent_ne_top)
    (by norm_num) (fun c => by simpa only [one_mul] using finitePathMap_bound f c)

lemma pathMap_finite (f : Family) (c : PathIndex f →₀ ℝ) :
    pathMap f (LpCoding.finite f.pathExponent c) = finitePathMap f c := by
  exact LinearMap.extendOfNorm_eq (f := finitePathMap f)
    (e := LpCoding.finite f.pathExponent)
    (LpCoding.finite_dense (ι := PathIndex f) (p := f.pathExponent) f.pathExponent_ne_top)
    ⟨1,fun c => by simpa only [one_mul] using finitePathMap_bound f c⟩ c

@[simp] lemma pathMap_single (f : Family) (P : PathIndex f) (a : ℝ) :
    pathMap f (lp.single f.pathExponent P a) = a • pathCoset P := by
  rw [← LpCoding.finite_single,pathMap_finite]
  simp [finitePathMap]

end SeparableQuotient.ActualSpace

namespace SeparableQuotient.Norming
open PathCoding CoherentClosures Cardinal
open scoped Classical Cardinal

lemma rawPath_card_le (hCH : Cardinal.mk ℝ = Cardinal.aleph 1) :
    Cardinal.mk RawPath ≤ Cardinal.mk Γ := by
  have hΓ : Cardinal.mk Γ = continuum := by
    rw [show Cardinal.mk Γ = Cardinal.aleph 1 by simp [Γ,OmegaOne],← hCH,Cardinal.mk_real]
  have hA : Cardinal.mk Array = continuum := by
    rw [Cardinal.mk_finsupp_of_infinite Γ ℚ,hΓ]
    simp [Cardinal.aleph0_le_continuum]
  let code : RawPath → (ℕ → Array × ℕ × ℕ) := fun P n => (P.piece n,P.weight n,P.metadata n)
  have hi : Function.Injective code := by
    intro P Q h
    apply RawPath.ext
    · funext n; exact congrArg Prod.fst (congrFun h n)
    · funext n; exact congrArg (fun x => x.2.1) (congrFun h n)
    · funext n; exact congrArg (fun x => x.2.2) (congrFun h n)
  calc
    Cardinal.mk RawPath ≤ Cardinal.mk (ℕ → Array × ℕ × ℕ) := Cardinal.mk_le_of_injective hi
    _ = continuum := by simp [Cardinal.mk_prod,hA]
    _ = Cardinal.mk Γ := hΓ.symm

lemma pathIndex_card_le (hCH : Cardinal.mk ℝ = Cardinal.aleph 1) (f : Family) :
    Cardinal.mk (PathIndex f) ≤ Cardinal.mk Γ :=
  (Cardinal.mk_subtype_le _).trans (rawPath_card_le hCH)

def pathLabelBase (hCH : Cardinal.mk ℝ = Cardinal.aleph 1) (f : Family) : PathIndex f ↪ Γ :=
  Classical.choice ((Cardinal.le_def _ _).mp (pathIndex_card_le hCH f))

def Family.index : Family → ℕ
  | .mixed => 0
  | .pure k => k+1

lemma Family.index_injective : Function.Injective Family.index := by
  intro f g h
  cases f <;> cases g <;> simp_all [Family.index]

def Family.sourceColor : Family → ℕ
  | .mixed => 1
  | .pure k => k+1

/-- An inner color partitions the shared C₁ while retaining the outer color. -/
def pathLabel (hCH : Cardinal.mk ℝ = Cardinal.aleph 1) (f : Family) (P : PathIndex f) : Γ :=
  Colors.inColor f.sourceColor (Colors.inColor f.index (pathLabelBase hCH f P))

@[simp] lemma pathLabel_color (hCH : Cardinal.mk ℝ = Cardinal.aleph 1) (f : Family) (P : PathIndex f) :
    Colors.color (pathLabel hCH f P) = f.sourceColor := by
  simp [pathLabel]

lemma pathLabel_injective (hCH : Cardinal.mk ℝ = Cardinal.aleph 1) :
    Function.Injective (fun z : (f : Family) × PathIndex f => pathLabel hCH z.1 z.2) := by
  rintro ⟨f,P⟩ ⟨g,Q⟩ h
  have hi := congrArg (fun a => (Colors.partitionEquiv a).2) h
  simp only [pathLabel,Colors.inColor,Equiv.apply_symm_apply] at hi
  have hf : f=g := Family.index_injective (by
    have hh := congrArg Colors.color hi
    simpa [Colors.color] using hh)
  subst g
  have hp : P=Q := (pathLabelBase hCH f).injective
    (Colors.inColor_injective _ hi)
  cases hp
  rfl

end SeparableQuotient.Norming

namespace SeparableQuotient.Norming
open scoped ENNReal

def Family.sourceExponent (f : Family) : ℝ≥0∞ := (Family.pure f.sourceColor).primalExponent
instance Family.sourceExponent_fact (f : Family) : Fact (1 ≤ f.sourceExponent) :=
  (Family.pure f.sourceColor).primalExponent_fact
@[simp] lemma Family.sourceExponent_real (f : Family) : f.sourceExponent.toReal = (f.s : ℝ)+1 := by
  change ((Family.pure f.sourceColor).primalExponent).toReal = _
  rw [Family.primalExponent_toReal]
  cases f <;> simp [Family.sourceColor,Family.s] <;> ring
lemma Family.sourceExponent_ne_top (f : Family) : f.sourceExponent ≠ ∞ := ENNReal.natCast_ne_top _
lemma Family.pathConjugate (f : Family) : f.sourceExponent.toReal.HolderConjugate f.pathExponent.toReal := by
  simpa only [Family.sourceExponent_real,Family.pathExponent_real,Family.q] using
    Parameters.sNext_q_conjugate f.s_ge_two

def pathLabelEmb (hCH : Cardinal.mk ℝ = Cardinal.aleph 1) (f : Family) : PathIndex f ↪ Γ where
  toFun := pathLabel hCH f
  inj' _ _ h := (pathLabelBase hCH f).injective
    (Colors.inColor_injective f.index (Colors.inColor_injective f.sourceColor h))

end SeparableQuotient.Norming

namespace SeparableQuotient.ActualSpace
open Norming NormConstruction PathCoding Filter
open scoped Classical Topology

variable (hCH : Cardinal.mk ℝ = Cardinal.aleph 1)

def finiteLabelMap (f : Family) : (PathIndex f →₀ ℝ) →ₗ[ℝ] E :=
  norming.includeFinite.comp (Finsupp.lmapDomain ℝ ℝ (pathLabel hCH f))

lemma finiteLabelMap_eq (f : Family) (c : PathIndex f →₀ ℝ) :
    finiteLabelMap hCH f c = norming.includeFinite (c.embDomain (pathLabelEmb hCH f)) := by
  rw [Finsupp.embDomain_eq_mapDomain]
  rfl

lemma finiteLabelMap_bound (f : Family) (c : PathIndex f →₀ ℝ) :
    ‖finiteLabelMap hCH f c‖ ≤ ‖LpCoding.finite f.sourceExponent c‖ := by
  rw [finiteLabelMap_eq]
  calc
    _ ≤ ‖LpFinite.realArray f.sourceExponent (c.embDomain (pathLabelEmb hCH f))‖ := by
      apply norm_includeFinite_on_color
      intro a ha
      rw [Finsupp.support_embDomain] at ha
      obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp ha
      exact pathLabel_color hCH f i
    _ = _ := by
      change ‖LpCoding.finite f.sourceExponent (c.embDomain (pathLabelEmb hCH f))‖ = _
      rw [LpCoding.norm_finite f.pathConjugate.pos,LpCoding.norm_finite f.pathConjugate.pos,
        Finsupp.support_embDomain,Finset.sum_map]
      simp only [Finsupp.embDomain_apply_self]

/-- The color synthesis operator. -/
def labelMap (f : Family) : lp (fun _ : PathIndex f => ℝ) f.sourceExponent →L[ℝ] E :=
  (finiteLabelMap hCH f).extendOfNorm (LpCoding.finite f.sourceExponent)

lemma norm_labelMap_le (f : Family) : ‖labelMap hCH f‖ ≤ 1 := by
  exact LinearMap.opNorm_extendOfNorm_le (f := finiteLabelMap hCH f)
    (e := LpCoding.finite f.sourceExponent)
    (LpCoding.finite_dense (ι := PathIndex f) (p := f.sourceExponent) f.sourceExponent_ne_top)
    (by norm_num) (fun c => by simpa only [one_mul] using finiteLabelMap_bound hCH f c)

lemma labelMap_finite (f : Family) (c : PathIndex f →₀ ℝ) :
    labelMap hCH f (LpCoding.finite f.sourceExponent c) = finiteLabelMap hCH f c := by
  exact LinearMap.extendOfNorm_eq (f := finiteLabelMap hCH f)
    (e := LpCoding.finite f.sourceExponent)
    (LpCoding.finite_dense (ι := PathIndex f) (p := f.sourceExponent) f.sourceExponent_ne_top)
    ⟨1,fun c => by simpa only [one_mul] using finiteLabelMap_bound hCH f c⟩ c

@[simp] lemma labelMap_single (f : Family) (P : PathIndex f) (a : ℝ) :
    labelMap hCH f (lp.single f.sourceExponent P a) = a • e (pathLabel hCH f P) := by
  rw [← LpCoding.finite_single,labelMap_finite,finiteLabelMap_eq,Finsupp.embDomain_single]
  change norming.includeFinite (Finsupp.single (pathLabel hCH f P) a) = _
  have hs : Finsupp.single (pathLabel hCH f P) a = a • Finsupp.single (pathLabel hCH f P) (1 : ℝ) := by
    simp
  rw [hs,map_smul]
  rfl

end SeparableQuotient.ActualSpace

end

end OAI
