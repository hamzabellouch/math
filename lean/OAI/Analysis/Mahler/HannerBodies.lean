import OAI.Analysis.Mahler.MainTheorem

namespace OAI

noncomputable section

namespace SymmetricMahler

open Set MeasureTheory

def hannerProduct {k l : ℕ} (A : Set (Fin k → ℝ)) (B : Set (Fin l → ℝ)) :
    Set (Fin (k + l) → ℝ) :=
  {z | ∃ x ∈ A, ∃ y ∈ B, z = Fin.append x y}

def hannerJoin {k l : ℕ} (A : Set (Fin k → ℝ)) (B : Set (Fin l → ℝ)) :
    Set (Fin (k + l) → ℝ) :=
  convexHull ℝ
    (((fun x : Fin k → ℝ => Fin.append x 0) '' A) ∪
      ((fun y : Fin l → ℝ => Fin.append 0 y) '' B))

inductive IsHanner : {n : ℕ} → Set (Fin n → ℝ) → Prop
  | interval (a : ℝ) (ha : 0 < a) :
      IsHanner (Icc (fun _ : Fin 1 => -a) (fun _ : Fin 1 => a))
  | product {k l : ℕ} {A : Set (Fin k → ℝ)} {B : Set (Fin l → ℝ)}
      (hA : IsHanner A) (hB : IsHanner B) : IsHanner (hannerProduct A B)
  | join {k l : ℕ} {A : Set (Fin k → ℝ)} {B : Set (Fin l → ℝ)}
      (hA : IsHanner A) (hB : IsHanner B) : IsHanner (hannerJoin A B)

def IsLinearHanner {n : ℕ} (K : Set (Fin n → ℝ)) : Prop :=
  ∃ H : Set (Fin n → ℝ), IsHanner H ∧
    ∃ T : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ), K = T '' H

structure RealNormData (E : Type*) [AddCommGroup E] [Module ℝ E] where
  toAddGroupNorm : AddGroupNorm E
  smul_eq : ∀ (a : ℝ) (x : E), toAddGroupNorm (a • x) = |a| * toAddGroupNorm x

namespace RealNormData
open MeasureTheory.Measure
variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

instance : CoeFun (RealNormData E) (fun _ => E → ℝ) := ⟨fun g => g.toAddGroupNorm⟩

@[simp] lemma apply_zero (g : RealNormData E) : g 0 = 0 := map_zero g.toAddGroupNorm
@[simp] lemma apply_neg (g : RealNormData E) (x : E) : g (-x) = g x :=
  map_neg_eq_map g.toAddGroupNorm x
lemma nonneg (g : RealNormData E) (x : E) : 0 ≤ g x := apply_nonneg g.toAddGroupNorm x
lemma add_le (g : RealNormData E) (x y : E) : g (x+y) ≤ g x + g y :=
  map_add_le_add g.toAddGroupNorm x y
@[simp] lemma eq_zero (g : RealNormData E) {x : E} : g x = 0 ↔ x = 0 :=
  ⟨g.toAddGroupNorm.eq_zero_of_map_eq_zero' x, fun h => h ▸ g.apply_zero⟩

def sum (g : RealNormData E) (h : RealNormData F) : RealNormData (E × F) where
  toAddGroupNorm := {
    toFun := fun z => g z.1 + h z.2
    map_zero' := by simp
    neg' := by intro x; simp
    add_le' := by intro x y; exact (add_le_add (g.add_le _ _) (h.add_le _ _)).trans_eq (by ring)
    eq_zero_of_map_eq_zero' := by
      rintro ⟨x,y⟩ he
      have hx : g x = 0 := le_antisymm (by linarith [h.nonneg y]) (g.nonneg x)
      have hy : h y = 0 := le_antisymm (by linarith [g.nonneg x]) (h.nonneg y)
      simp_all }
  smul_eq := by
    intro a x
    change g (a • x.1) + h (a • x.2) = |a| * (g x.1 + h x.2)
    rw [g.smul_eq, h.smul_eq]; ring

def max (g : RealNormData E) (h : RealNormData F) : RealNormData (E × F) where
  toAddGroupNorm := {
    toFun := fun z => Max.max (g z.1) (h z.2)
    map_zero' := by simp
    neg' := by intro x; simp
    add_le' := by
      intro x y
      exact max_le
        ((g.add_le _ _).trans (add_le_add (le_max_left _ _) (le_max_left _ _)))
        ((h.add_le _ _).trans (add_le_add (le_max_right _ _) (le_max_right _ _)))
    eq_zero_of_map_eq_zero' := by
      rintro ⟨x,y⟩ he
      have hx : g x = 0 := le_antisymm ((le_max_left _ _).trans he.le) (g.nonneg x)
      have hy : h y = 0 := le_antisymm ((le_max_right _ _).trans he.le) (h.nonneg y)
      simp_all }
  smul_eq := by
    intro a x
    change Max.max (g (a • x.1)) (h (a • x.2)) = |a| * Max.max (g x.1) (h x.2)
    rw [g.smul_eq, h.smul_eq, mul_max_of_nonneg _ _ (abs_nonneg a)]

@[simp] lemma sum_apply (g : RealNormData E) (h : RealNormData F) (z : E×F) :
    g.sum h z = g z.1 + h z.2 := rfl
@[simp] lemma max_apply (g : RealNormData E) (h : RealNormData F) (z : E×F) :
    g.max h z = Max.max (g z.1) (h z.2) := rfl

def unit (g : RealNormData E) : Set E := {x | g x ≤ 1}

@[simp] lemma zero_mem_unit (g : RealNormData E) : 0 ∈ g.unit := by simp [unit]
lemma unit_max (g : RealNormData E) (h : RealNormData F) :
    (g.max h).unit = g.unit ×ˢ h.unit := by ext x; simp [unit]

lemma convex_unit (g : RealNormData E) : Convex ℝ g.unit := by
  intro x hx y hy a b ha hb hab
  change g (a • x + b • y) ≤ 1
  calc
    g (a • x + b • y) ≤ g (a • x) + g (b • y) := g.add_le _ _
    _ = a * g x + b * g y := by rw [g.smul_eq, g.smul_eq, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * 1 + b * 1 := add_le_add (mul_le_mul_of_nonneg_left hx ha)
      (mul_le_mul_of_nonneg_left hy hb)
    _ = 1 := by linarith

lemma exists_smul_unit (g : RealNormData E) {r : ℝ} (hr : 0 ≤ r) {x : E} (hx : g x ≤ r) :
    ∃ u ∈ g.unit, x = r • u := by
  obtain rfl | hr := hr.eq_or_lt
  · have hx0 : x = 0 := g.eq_zero.mp (le_antisymm hx (g.nonneg x))
    exact ⟨0, g.zero_mem_unit, by simp [hx0]⟩
  refine ⟨r⁻¹ • x, ?_, ?_⟩
  · change g (r⁻¹ • x) ≤ 1
    rw [g.smul_eq, abs_of_pos (inv_pos.mpr hr)]
    exact (inv_mul_le_one₀ hr).mpr hx
  · simp [smul_smul, ne_of_gt hr]

lemma unit_sum (g : RealNormData E) (h : RealNormData F) :
    (g.sum h).unit = convexHull ℝ
      (((fun x : E => (x, (0:F))) '' g.unit) ∪ ((fun y : F => ((0:E), y)) '' h.unit)) := by
  apply subset_antisymm
  · rintro ⟨x,y⟩ hxy
    change g x + h y ≤ 1 at hxy
    obtain ⟨u, hu, hx⟩ := g.exists_smul_unit (g.nonneg x) (le_refl (g x))
    obtain ⟨v, hv, hy⟩ := h.exists_smul_unit (show 0 ≤ 1-g x by linarith [h.nonneg y])
      (show h y ≤ 1-g x by linarith)
    have hh := (convex_convexHull ℝ
      (((fun x : E => (x, (0:F))) '' g.unit) ∪ ((fun y : F => ((0:E), y)) '' h.unit)))
      (subset_convexHull ℝ _ (Or.inl ⟨u,hu,rfl⟩))
      (subset_convexHull ℝ _ (Or.inr ⟨v,hv,rfl⟩))
      (g.nonneg x) (show 0 ≤ 1-g x by linarith [h.nonneg y]) (by ring : g x + (1-g x) = 1)
    convert hh using 1
    ext <;> simp [←hx, ←hy]
  · apply convexHull_min _ (g.sum h).convex_unit
    rintro _ (⟨x,hx,rfl⟩ | ⟨y,hy,rfl⟩)
    · simpa only [unit, Set.mem_ofPred_eq, sum_apply, apply_zero, add_zero] using hx
    · simpa only [unit, Set.mem_ofPred_eq, sum_apply, apply_zero, zero_add] using hy

def comap (g : RealNormData E) (e : F ≃ₗ[ℝ] E) : RealNormData F where
  toAddGroupNorm := {
    toFun := fun x => g (e x)
    map_zero' := by simp
    neg' := by intro x; simp
    add_le' := by intro x y; simpa only [map_add] using g.add_le (e x) (e y)
    eq_zero_of_map_eq_zero' := by intro x hx; exact e.injective (by simpa using g.eq_zero.mp hx) }
  smul_eq := by
    intro a x
    change g (e (a • x)) = |a| * g (e x)
    rw [map_smul, g.smul_eq]

@[simp] lemma comap_apply (g : RealNormData E) (e : F ≃ₗ[ℝ] E) (x : F) :
    g.comap e x = g (e x) := rfl

lemma unit_comap (g : RealNormData E) (e : F ≃ₗ[ℝ] E) :
    (g.comap e).unit = e.symm '' g.unit := by
  ext x
  constructor
  · intro hx
    exact ⟨e x, hx, e.symm_apply_apply x⟩
  · rintro ⟨y,hy,rfl⟩
    simpa only [unit, comap_apply, Set.mem_ofPred_eq, e.apply_symm_apply] using hy

variable [inst423 : TopologicalSpace E] [inst424 : IsTopologicalAddGroup E] [inst425 : T2Space E] [inst426 : ContinuousSMul ℝ E]
  [MeasurableSpace E] [inst428 : BorelSpace E] [inst429 : FiniteDimensional ℝ E] [inst430 : SecondCountableTopology E]
  [inst431 : TopologicalSpace F] [inst432 : IsTopologicalAddGroup F] [inst433 : T2Space F] [inst434 : ContinuousSMul ℝ F]
  [MeasurableSpace F] [inst436 : BorelSpace F] [inst437 : FiniteDimensional ℝ F] [inst438 : SecondCountableTopology F]

omit inst430 in
lemma measure_unit [SecondCountableTopology E] (g : RealNormData E) (μ : Measure E) [IsAddHaarMeasure μ] [Nontrivial E] :
    μ g.unit = ENNReal.ofReal ((∫ x, Real.exp (-g x) ∂μ) / (Nat.factorial (Module.finrank ℝ E) : ℝ)) := by
  rw [unit, MeasureTheory.measure_le_eq_lt μ g.apply_zero g.apply_neg g.add_le
    (fun hx => g.eq_zero.mp hx) (fun a x => (g.smul_eq a x).le) 1]
  have hh := MeasureTheory.measure_lt_one_eq_integral_div_gamma μ g.apply_zero g.apply_neg g.add_le
    (fun hx => g.eq_zero.mp hx) (fun a x => (g.smul_eq a x).le) (show (0:ℝ) < 1 by norm_num)
  simpa only [div_one, Real.rpow_one, Real.Gamma_nat_eq_factorial] using hh

lemma measureReal_unit (g : RealNormData E) (μ : Measure E) [IsAddHaarMeasure μ] [Nontrivial E] :
    (μ g.unit).toReal = (∫ x, Real.exp (-g x) ∂μ) / (Nat.factorial (Module.finrank ℝ E) : ℝ) := by
  rw [g.measure_unit μ, ENNReal.toReal_ofReal]
  exact div_nonneg (integral_nonneg fun _ => (Real.exp_pos _).le) (by positivity)

lemma measureReal_unit_sum (g : RealNormData E) (h : RealNormData F)
    (μ : Measure E) (ν : Measure F) [IsAddHaarMeasure μ] [IsAddHaarMeasure ν]
    [SigmaFinite μ] [SigmaFinite ν] [Nontrivial E] [Nontrivial F] :
    ((μ.prod ν) (g.sum h).unit).toReal =
      (Nat.factorial (Module.finrank ℝ E) : ℝ) * Nat.factorial (Module.finrank ℝ F) /
        Nat.factorial (Module.finrank ℝ E + Module.finrank ℝ F) *
      (μ g.unit).toReal * (ν h.unit).toReal := by
  rw [(g.sum h).measureReal_unit, g.measureReal_unit, h.measureReal_unit]
  simp_rw [sum_apply, neg_add, Real.exp_add]
  rw [integral_prod_mul (μ := μ) (ν := ν) (fun x : E => Real.exp (-g x))
    (fun y : F => Real.exp (-h y)), Module.finrank_prod]
  have hE : (Nat.factorial (Module.finrank ℝ E) : ℝ) ≠ 0 := by positivity
  have hF : (Nat.factorial (Module.finrank ℝ F) : ℝ) ≠ 0 := by positivity
  field_simp

omit inst423 inst424 inst425 inst426 inst428 inst429 inst430 inst431 inst432 inst433 inst434 inst436 inst437 inst438 in
lemma measureReal_unit_max [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E] [ContinuousSMul ℝ E] [BorelSpace E] [FiniteDimensional ℝ E] [SecondCountableTopology E] [TopologicalSpace F] [IsTopologicalAddGroup F] [T2Space F] [ContinuousSMul ℝ F] [BorelSpace F] [FiniteDimensional ℝ F] [SecondCountableTopology F] (g : RealNormData E) (h : RealNormData F)
    (μ : Measure E) (ν : Measure F) [SigmaFinite ν] :
    ((μ.prod ν) (g.max h).unit).toReal = (μ g.unit).toReal * (ν h.unit).toReal := by
  rw [unit_max, Measure.prod_prod, ENNReal.toReal_mul]

end RealNormData

def appendEquiv (k l : ℕ) : ((Fin k → ℝ) × (Fin l → ℝ)) ≃ₗ[ℝ] (Fin (k+l) → ℝ) where
  toFun z := Fin.append z.1 z.2
  invFun z := (fun i => z (Fin.castAdd l i), fun i => z (Fin.natAdd k i))
  left_inv z := by ext <;> simp
  right_inv z := by ext i; refine Fin.addCases (fun _ => ?_) (fun _ => ?_) i <;> simp
  map_add' z w := by ext i; refine Fin.addCases (fun _ => ?_) (fun _ => ?_) i <;> simp
  map_smul' a z := by ext i; refine Fin.addCases (fun _ => ?_) (fun _ => ?_) i <;> simp

@[simp] lemma appendEquiv_apply {k l : ℕ} (x : Fin k → ℝ) (y : Fin l → ℝ) :
    appendEquiv k l (x,y) = Fin.append x y := rfl

lemma measurePreserving_appendEquiv (k l : ℕ) : MeasurePreserving (appendEquiv k l) := by
  let e₁ := (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin k ⊕ Fin l => ℝ)).symm
  let e₂ := MeasurableEquiv.piCongrLeft (fun _ : Fin (k+l) => ℝ) (finSumFinEquiv : Fin k ⊕ Fin l ≃ _)
  have h₁ : MeasurePreserving e₁ := volume_measurePreserving_sumPiEquivProdPi_symm _
  have h₂ : MeasurePreserving e₂ := volume_measurePreserving_piCongrLeft _ _
  convert h₂.comp h₁ using 1
  funext z i
  refine Fin.addCases (fun _ => ?_) (fun _ => ?_) i <;>
    simp [e₁, e₂, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, Equiv.piCongrLeft',
      MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi, appendEquiv]

lemma volume_appendEquiv_image {k l : ℕ} (S : Set ((Fin k → ℝ) × (Fin l → ℝ))) :
    volume (appendEquiv k l '' S) = volume S :=
  by
    have hh := (measurePreserving_appendEquiv k l).measure_preimage_emb
      (appendEquiv k l).toContinuousLinearEquiv.toHomeomorph.measurableEmbedding
      (appendEquiv k l '' S)
    rw [Set.preimage_image_eq _ (appendEquiv k l).injective] at hh
    exact hh.symm

lemma dot_append {k l : ℕ} (x p : Fin k → ℝ) (y q : Fin l → ℝ) :
    (∑ i, Fin.append p q i * Fin.append x y i) = (∑ i, p i*x i) + ∑ i, q i*y i := by
  rw [Fin.sum_univ_add]
  simp

lemma hannerProduct_eq_append_image {k l : ℕ} (A : Set (Fin k → ℝ)) (B : Set (Fin l → ℝ)) :
    hannerProduct A B = appendEquiv k l '' (A ×ˢ B) := by
  ext z
  constructor
  · rintro ⟨x,hx,y,hy,rfl⟩
    exact ⟨(x,y), ⟨hx,hy⟩, rfl⟩
  · rintro ⟨⟨x,y⟩, ⟨hx,hy⟩, rfl⟩
    exact ⟨x,hx,y,hy,rfl⟩

namespace RealNormData

def coordSum {k l : ℕ} (g : RealNormData (Fin k → ℝ)) (h : RealNormData (Fin l → ℝ)) :
    RealNormData (Fin (k+l) → ℝ) := (g.sum h).comap (appendEquiv k l).symm

def coordMax {k l : ℕ} (g : RealNormData (Fin k → ℝ)) (h : RealNormData (Fin l → ℝ)) :
    RealNormData (Fin (k+l) → ℝ) := (g.max h).comap (appendEquiv k l).symm

@[simp] lemma coordSum_append {k l : ℕ} (g : RealNormData (Fin k → ℝ))
    (h : RealNormData (Fin l → ℝ)) (x : Fin k → ℝ) (y : Fin l → ℝ) :
    g.coordSum h (Fin.append x y) = g x + h y := by
  change g.sum h ((appendEquiv k l).symm (appendEquiv k l (x,y))) = _
  rw [LinearEquiv.symm_apply_apply]; rfl

@[simp] lemma coordMax_append {k l : ℕ} (g : RealNormData (Fin k → ℝ))
    (h : RealNormData (Fin l → ℝ)) (x : Fin k → ℝ) (y : Fin l → ℝ) :
    g.coordMax h (Fin.append x y) = Max.max (g x) (h y) := by
  change g.max h ((appendEquiv k l).symm (appendEquiv k l (x,y))) = _
  rw [LinearEquiv.symm_apply_apply]; rfl

lemma unit_coordMax {k l : ℕ} (g : RealNormData (Fin k → ℝ)) (h : RealNormData (Fin l → ℝ)) :
    (g.coordMax h).unit = hannerProduct g.unit h.unit := by
  rw [coordMax, unit_comap, unit_max, hannerProduct_eq_append_image]
  rfl

lemma unit_coordSum {k l : ℕ} (g : RealNormData (Fin k → ℝ)) (h : RealNormData (Fin l → ℝ)) :
    (g.coordSum h).unit = hannerJoin g.unit h.unit := by
  rw [coordSum, unit_comap, unit_sum, LinearEquiv.symm_symm]
  change (appendEquiv k l).toLinearMap '' convexHull ℝ _ = _
  rw [LinearMap.image_convexHull]
  simp only [hannerJoin, image_union, image_image]
  rfl

lemma volumeReal_unit_coordMax {k l : ℕ} (g : RealNormData (Fin k → ℝ)) (h : RealNormData (Fin l → ℝ)) :
    (volume (g.coordMax h).unit).toReal = (volume g.unit).toReal * (volume h.unit).toReal := by
  rw [coordMax, unit_comap, LinearEquiv.symm_symm, volume_appendEquiv_image]
  exact g.measureReal_unit_max h volume volume

lemma volumeReal_unit_coordSum {k l : ℕ} (hk : 0 < k) (hl : 0 < l)
    (g : RealNormData (Fin k → ℝ)) (h : RealNormData (Fin l → ℝ)) :
    (volume (g.coordSum h).unit).toReal = (Nat.factorial k : ℝ) * Nat.factorial l / Nat.factorial (k+l) *
      (volume g.unit).toReal * (volume h.unit).toReal := by
  have : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  have : Nonempty (Fin l) := Fin.pos_iff_nonempty.mp hl
  rw [coordSum, unit_comap, LinearEquiv.symm_symm, volume_appendEquiv_image]
  change (((volume : Measure (Fin k → ℝ)).prod (volume : Measure (Fin l → ℝ)))
    (g.sum h).unit).toReal = _
  simpa only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin, mul_one] using
    g.measureReal_unit_sum h volume volume

def interval (a : ℝ) (ha : 0 < a) : RealNormData (Fin 1 → ℝ) where
  toAddGroupNorm := {
    toFun := fun x => |x 0| / a
    map_zero' := by simp
    add_le' := by intro x y; simpa [add_div] using (div_le_div_of_nonneg_right (abs_add_le (x 0) (y 0)) ha.le)
    neg' := by intro x; simp
    eq_zero_of_map_eq_zero' := by
      intro x hx
      have h : x 0 = 0 := abs_eq_zero.mp ((div_eq_zero_iff).mp hx |>.resolve_right (ne_of_gt ha))
      ext i; fin_cases i; exact h }
  smul_eq := by
    intro t x
    change |t * x 0| / a = |t| * (|x 0| / a)
    rw [abs_mul]
    ring

@[simp] lemma interval_apply (a : ℝ) (ha : 0 < a) (x : Fin 1 → ℝ) :
    interval a ha x = |x 0| / a := rfl

lemma unit_interval (a : ℝ) (ha : 0 < a) :
    (interval a ha).unit = Icc (fun _ : Fin 1 => -a) (fun _ => a) := by
  ext x
  simp only [unit, Set.mem_ofPred_eq, interval_apply, div_le_one ha, abs_le, mem_Icc,
    Pi.le_def, Fin.forall_fin_one]

lemma volumeReal_unit_interval (a : ℝ) (ha : 0 < a) :
    (volume (interval a ha).unit).toReal = 2*a := by
  rw [unit_interval, Real.volume_Icc_pi]
  simp only [Fin.prod_univ_one, sub_neg_eq_add, ENNReal.toReal_ofReal (by linarith : 0 ≤ a+a)]
  ring

def IsDual {n : ℕ} (g h : RealNormData (Fin n → ℝ)) : Prop :=
  (∀ x p, (∑ i, p i*x i) ≤ g x * h p) ∧
  (∀ p, ∃ x ∈ g.unit, (∑ i, p i*x i) = h p)

lemma IsDual.polar_unit {n : ℕ} {g h : RealNormData (Fin n → ℝ)} (hd : g.IsDual h) :
    coordinatePolar g.unit = h.unit := by
  ext p
  constructor
  · intro hp
    obtain ⟨x,hx,he⟩ := hd.2 p
    change h p ≤ 1
    rw [← he]
    exact hp x hx
  · intro hp x hx
    change h p ≤ 1 at hp
    exact (hd.1 x p).trans <|
      (mul_le_mul_of_nonneg_right hx (h.nonneg p)).trans (by simpa using hp)

lemma interval_isDual (a : ℝ) (ha : 0 < a) :
    (interval a ha).IsDual (interval a⁻¹ (inv_pos.mpr ha)) := by
  constructor
  · intro x p
    simp only [Fin.sum_univ_one, interval_apply, div_inv_eq_mul]
    calc
      p 0 * x 0 ≤ |p 0 * x 0| := le_abs_self _
      _ = |x 0| / a * (|p 0| * a) := by rw [abs_mul]; field_simp
  · intro p
    by_cases hp : 0 ≤ p 0
    · refine ⟨fun _ => a, ?_, ?_⟩
      · simp [unit, abs_of_pos ha, ne_of_gt ha]
      · simp [abs_of_nonneg hp]
    · refine ⟨fun _ => -a, ?_, ?_⟩
      · simp [unit, abs_of_pos ha, ne_of_gt ha]
      · simp [abs_of_neg (lt_of_not_ge hp)]

theorem IsDual.coordMax_sum {k l : ℕ} {g g' : RealNormData (Fin k → ℝ)}
    {h h' : RealNormData (Fin l → ℝ)} (hg : g.IsDual g') (hh : h.IsDual h') :
    (g.coordMax h).IsDual (g'.coordSum h') := by
  constructor
  · intro x p
    obtain ⟨⟨x₁,x₂⟩,rfl⟩ := (appendEquiv k l).surjective x
    obtain ⟨⟨p₁,p₂⟩,rfl⟩ := (appendEquiv k l).surjective p
    simp only [appendEquiv_apply, coordMax_append, coordSum_append, dot_append]
    calc
      _ ≤ g x₁ * g' p₁ + h x₂ * h' p₂ := add_le_add (hg.1 _ _) (hh.1 _ _)
      _ ≤ Max.max (g x₁) (h x₂) * g' p₁ + Max.max (g x₁) (h x₂) * h' p₂ :=
        add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) (g'.nonneg _))
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (h'.nonneg _))
      _ = _ := by ring
  · intro p
    obtain ⟨⟨p₁,p₂⟩,rfl⟩ := (appendEquiv k l).surjective p
    obtain ⟨x,hx,hxp⟩ := hg.2 p₁
    obtain ⟨y,hy,hyp⟩ := hh.2 p₂
    refine ⟨Fin.append x y, ?_, ?_⟩
    · simpa only [unit, Set.mem_ofPred_eq, coordMax_append, max_le_iff] using And.intro hx hy
    · simp only [appendEquiv_apply, dot_append, coordSum_append, hxp, hyp]

theorem IsDual.coordSum_max {k l : ℕ} {g g' : RealNormData (Fin k → ℝ)}
    {h h' : RealNormData (Fin l → ℝ)} (hg : g.IsDual g') (hh : h.IsDual h') :
    (g.coordSum h).IsDual (g'.coordMax h') := by
  constructor
  · intro x p
    obtain ⟨⟨x₁,x₂⟩,rfl⟩ := (appendEquiv k l).surjective x
    obtain ⟨⟨p₁,p₂⟩,rfl⟩ := (appendEquiv k l).surjective p
    simp only [appendEquiv_apply, coordMax_append, coordSum_append, dot_append]
    calc
      _ ≤ g x₁ * g' p₁ + h x₂ * h' p₂ := add_le_add (hg.1 _ _) (hh.1 _ _)
      _ ≤ g x₁ * Max.max (g' p₁) (h' p₂) + h x₂ * Max.max (g' p₁) (h' p₂) :=
        add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) (g.nonneg _))
          (mul_le_mul_of_nonneg_left (le_max_right _ _) (h.nonneg _))
      _ = _ := by ring
  · intro p
    obtain ⟨⟨p₁,p₂⟩,rfl⟩ := (appendEquiv k l).surjective p
    obtain ⟨x,hx,hxp⟩ := hg.2 p₁
    obtain ⟨y,hy,hyp⟩ := hh.2 p₂
    rcases le_total (h' p₂) (g' p₁) with hp | hp
    · refine ⟨Fin.append x 0, ?_, ?_⟩
      · simpa only [unit, Set.mem_ofPred_eq, coordSum_append, apply_zero, add_zero] using hx
      · simp only [appendEquiv_apply, dot_append, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
          add_zero, hxp, coordMax_append, max_eq_left hp]
    · refine ⟨Fin.append 0 y, ?_, ?_⟩
      · simpa only [unit, Set.mem_ofPred_eq, coordSum_append, apply_zero, zero_add] using hy
      · simp only [appendEquiv_apply, dot_append, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
          zero_add, hyp, coordMax_append, max_eq_right hp]

end RealNormData

lemma IsHanner.dim_pos {n : ℕ} {K : Set (Fin n → ℝ)} (hK : IsHanner K) : 0 < n := by
  induction hK with
  | interval a ha => omega
  | product hA hB ihA ihB => omega
  | join hA hB ihA ihB => omega

lemma hanner_volume_recursion {k l : ℕ} {v v' w w' : ℝ}
    (h₁ : v*v' = (4:ℝ)^k / Nat.factorial k)
    (h₂ : w*w' = (4:ℝ)^l / Nat.factorial l) :
    (v*w) * ((Nat.factorial k : ℝ) * Nat.factorial l / Nat.factorial (k+l) * v' * w') =
      (4:ℝ)^(k+l) / Nat.factorial (k+l) := by
  calc
    _ = ((Nat.factorial k : ℝ) * Nat.factorial l / Nat.factorial (k+l)) * (v*v') * (w*w') := by ring
    _ = _ := by
      rw [h₁, h₂, pow_add]
      have hfk : (Nat.factorial k : ℝ) ≠ 0 := by positivity
      have hfl : (Nat.factorial l : ℝ) ≠ 0 := by positivity
      field_simp

theorem IsHanner.gauges {n : ℕ} {K : Set (Fin n → ℝ)} (hK : IsHanner K) :
    ∃ g h : RealNormData (Fin n → ℝ), K = g.unit ∧ g.IsDual h ∧ IsHanner h.unit ∧
      (volume g.unit).toReal * (volume h.unit).toReal = (4:ℝ)^n / Nat.factorial n := by
  induction hK with
  | interval a ha =>
    refine ⟨.interval a ha, .interval a⁻¹ (inv_pos.mpr ha), ?_,
      RealNormData.interval_isDual a ha, ?_, ?_⟩
    · exact (RealNormData.unit_interval a ha).symm
    · rw [RealNormData.unit_interval]
      exact IsHanner.interval a⁻¹ (inv_pos.mpr ha)
    · rw [RealNormData.volumeReal_unit_interval, RealNormData.volumeReal_unit_interval]
      norm_num
      field_simp
      norm_num
  | @product k l A B hA hB ihA ihB =>
    obtain ⟨g,g',hAg,hgd,hgH,hgv⟩ := ihA
    obtain ⟨h,h',hBh,hhd,hhH,hhv⟩ := ihB
    refine ⟨g.coordMax h, g'.coordSum h', ?_, hgd.coordMax_sum hhd, ?_, ?_⟩
    · rw [RealNormData.unit_coordMax, hAg, hBh]
    · rw [RealNormData.unit_coordSum]
      exact IsHanner.join hgH hhH
    · rw [RealNormData.volumeReal_unit_coordMax,
        RealNormData.volumeReal_unit_coordSum hA.dim_pos hB.dim_pos]
      exact hanner_volume_recursion hgv hhv
  | @join k l A B hA hB ihA ihB =>
    obtain ⟨g,g',hAg,hgd,hgH,hgv⟩ := ihA
    obtain ⟨h,h',hBh,hhd,hhH,hhv⟩ := ihB
    refine ⟨g.coordSum h, g'.coordMax h', ?_, hgd.coordSum_max hhd, ?_, ?_⟩
    · rw [RealNormData.unit_coordSum, hAg, hBh]
    · rw [RealNormData.unit_coordMax]
      exact IsHanner.product hgH hhH
    · rw [RealNormData.volumeReal_unit_coordSum hA.dim_pos hB.dim_pos,
        RealNormData.volumeReal_unit_coordMax, mul_comm]
      exact hanner_volume_recursion (by simpa only [mul_comm] using hgv)
        (by simpa only [mul_comm] using hhv)

theorem IsHanner.polar {n : ℕ} {K : Set (Fin n → ℝ)} (hK : IsHanner K) :
    IsHanner (coordinatePolar K) := by
  obtain ⟨g,h,rfl,hd,hH,-⟩ := hK.gauges
  rwa [hd.polar_unit]

theorem IsHanner.volumeProduct {n : ℕ} {K : Set (Fin n → ℝ)} (hK : IsHanner K) :
    (volume K).toReal * (volume (coordinatePolar K)).toReal = (4:ℝ)^n / Nat.factorial n := by
  obtain ⟨g,h,rfl,hd,-,hv⟩ := hK.gauges
  rwa [hd.polar_unit]

def coordinateTransposeMap {n : ℕ} (T : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) :
    (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
  Matrix.toLin' (LinearMap.toMatrix' T).transpose

lemma det_coordinateTransposeMap {n : ℕ} (T : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) :
    LinearMap.det (coordinateTransposeMap T) = LinearMap.det T := by
  rw [← LinearMap.det_toMatrix', coordinateTransposeMap, LinearMap.toMatrix'_toLin',
    Matrix.det_transpose, LinearMap.det_toMatrix']

def coordinateTranspose {n : ℕ} (T : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) :
    (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) :=
  (coordinateTransposeMap T.toLinearMap).equivOfDetNeZero
    (by rw [det_coordinateTransposeMap]; exact T.isUnit_det'.ne_zero)

lemma coordinateTranspose_apply {n : ℕ} (T : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ))
    (p x : Fin n → ℝ) :
    (∑ i, coordinateTranspose T p i * x i) = ∑ i, p i * T x i := by
  change (Matrix.toLin' (LinearMap.toMatrix' T.toLinearMap).transpose p) ⬝ᵥ x =
    p ⬝ᵥ T.toLinearMap x
  rw [Matrix.toLin'_apply, dotProduct_comm]
  rw [Matrix.dotProduct_transpose_mulVec]
  rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']

lemma det_coordinateTranspose {n : ℕ} (T : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) :
    LinearMap.det (coordinateTranspose T).toLinearMap = LinearMap.det T.toLinearMap :=
  det_coordinateTransposeMap _

lemma coordinatePolar_image {n : ℕ} (T : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ))
    (K : Set (Fin n → ℝ)) :
    coordinatePolar (T '' K) = coordinateTranspose T ⁻¹' coordinatePolar K := by
  ext p
  simp only [coordinatePolar, Set.mem_ofPred_eq, mem_preimage, forall_mem_image,
    coordinateTranspose_apply]

lemma coordinatePolar_image_eq {n : ℕ} (T : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ))
    (K : Set (Fin n → ℝ)) :
    coordinatePolar (T '' K) = (coordinateTranspose T).symm '' coordinatePolar K := by
  rw [coordinatePolar_image, LinearEquiv.image_eq_preimage_symm, LinearEquiv.symm_symm]

theorem volumeProduct_linear_image {n : ℕ}
    (T : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) (K : Set (Fin n → ℝ)) :
    (volume (T '' K)).toReal * (volume (coordinatePolar (T '' K))).toReal =
      (volume K).toReal * (volume (coordinatePolar K)).toReal := by
  rw [coordinatePolar_image]
  have hi := Measure.addHaar_image_linearMap volume T.toLinearMap K
  change volume (T '' K) = _ at hi
  rw [hi, Measure.addHaar_preimage_linearEquiv, LinearEquiv.det_coe_symm,
    det_coordinateTranspose, abs_inv, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_ofReal (inv_nonneg.mpr (abs_nonneg _))]
  have hd : |LinearMap.det T.toLinearMap| ≠ 0 := abs_ne_zero.mpr T.isUnit_det'.ne_zero
  field_simp

theorem IsLinearHanner.volumeProduct {n : ℕ} {K : Set (Fin n → ℝ)}
    (hK : IsLinearHanner K) :
    (volume K).toReal * (volume (coordinatePolar K)).toReal = (4:ℝ)^n / Nat.factorial n := by
  obtain ⟨H,hH,T,rfl⟩ := hK
  rw [volumeProduct_linear_image]
  exact hH.volumeProduct

theorem IsLinearHanner.polar {n : ℕ} {K : Set (Fin n → ℝ)}
    (hK : IsLinearHanner K) : IsLinearHanner (coordinatePolar K) := by
  obtain ⟨H,hH,T,rfl⟩ := hK
  exact ⟨coordinatePolar H, hH.polar, (coordinateTranspose T).symm,
    coordinatePolar_image_eq T H⟩

open Set Metric MeasureTheory
open scoped Topology Pointwise
namespace RealNormData

section Algebra
variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def Space (_ : RealNormData E) := E

namespace Space
instance (g : RealNormData E) : AddCommGroup g.Space := (inferInstance : AddCommGroup E)
instance (g : RealNormData E) : Module ℝ g.Space := (inferInstance : Module ℝ E)
instance (g : RealNormData E) : NormedAddCommGroup g.Space :=
  g.toAddGroupNorm.toNormedAddCommGroup
instance (g : RealNormData E) : NormedSpace ℝ g.Space where
  toModule := (inferInstance : Module ℝ E)
  norm_smul_le a x := by
    change g (a • x) ≤ ‖a‖ * g x
    exact (g.smul_eq a x).le
instance (g : RealNormData E) [FiniteDimensional ℝ E] : FiniteDimensional ℝ g.Space :=
  (inferInstance : FiniteDimensional ℝ E)
instance (g : RealNormData E) [Nontrivial E] : Nontrivial g.Space :=
  (inferInstance : Nontrivial E)
end Space

def spaceEquiv (g : RealNormData E) : g.Space ≃ₗ[ℝ] E := LinearEquiv.refl ℝ E

@[simp] lemma space_norm (g : RealNormData E) (x : g.Space) : ‖x‖ = g (g.spaceEquiv x) := rfl

end Algebra
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [inst443 : FiniteDimensional ℝ E]

lemma continuous (g : RealNormData E) : Continuous g := by
  exact continuous_norm.comp g.spaceEquiv.symm.toContinuousLinearEquiv.continuous

omit inst443 in
lemma unit_eq_image_closedBall [FiniteDimensional ℝ E] (g : RealNormData E) :
    g.unit = g.spaceEquiv '' closedBall (0:g.Space) 1 := by
  ext x
  constructor
  · intro hx
    exact ⟨g.spaceEquiv.symm x, by simpa only [mem_closedBall_zero_iff,space_norm,LinearEquiv.apply_symm_apply,unit,Set.mem_ofPred_eq] using hx, g.spaceEquiv.apply_symm_apply x⟩
  · rintro ⟨y,hy,rfl⟩
    simpa only [mem_closedBall_zero_iff,space_norm,unit,Set.mem_ofPred_eq] using hy

lemma isCompact_unit (g : RealNormData E) : IsCompact g.unit := by
  rw [g.unit_eq_image_closedBall]
  exact (isCompact_closedBall (0:g.Space) 1).image g.spaceEquiv.toContinuousLinearEquiv.continuous

lemma unit_nhds (g : RealNormData E) : g.unit ∈ 𝓝 (0:E) := by
  have hh : ∀ᶠ x in 𝓝 (0:E), g x < 1 :=
    (g.continuous.tendsto 0).eventually (Iio_mem_nhds (by simp))
  exact Filter.mem_of_superset hh (fun x hx => (show g x < 1 from hx).le)

omit inst443 in
lemma symmetric_unit [FiniteDimensional ℝ E] (g : RealNormData E) : ∀ x ∈ g.unit, -x ∈ g.unit := by
  intro x hx
  simpa only [unit,Set.mem_ofPred_eq,g.apply_neg] using hx

lemma interior_unit_nonempty (g : RealNormData E) : (interior g.unit).Nonempty :=
  ⟨0,mem_interior_iff_mem_nhds.mpr g.unit_nhds⟩

end RealNormData

lemma body_nhds_zero {n : ℕ} {B : Set (Fin n → ℝ)} (hc : Convex ℝ B)
    (hs : ∀ x ∈ B, -x ∈ B) (hi : (interior B).Nonempty) : B ∈ 𝓝 (0:Fin n → ℝ) :=
  mem_interior_iff_mem_nhds.mp (zero_mem_interior_of_symmetric hc hs hi)

def bodyNorm {n : ℕ} {B : Set (Fin n → ℝ)} (hB : IsCompact B) (hc : Convex ℝ B)
    (hs : ∀ x ∈ B, -x ∈ B) (hi : (interior B).Nonempty) : RealNormData (Fin n → ℝ) where
  toAddGroupNorm := {
    toFun := gauge B
    map_zero' := gauge_zero
    neg' := by
      intro x
      have hh := gauge_smul ((balanced_iff_neg_mem hc).mpr (fun x hx => hs x hx)) (-1:ℝ) x
      simpa only [neg_one_smul,norm_neg,norm_one,one_mul] using hh
    add_le' := gauge_add_le hc (absorbent_nhds_zero (body_nhds_zero hc hs hi))
    eq_zero_of_map_eq_zero' := fun x hx =>
      (gauge_eq_zero (absorbent_nhds_zero (body_nhds_zero hc hs hi)) (hB.isVonNBounded (𝕜 := ℝ))).mp hx }
  smul_eq := by
    intro a x
    exact gauge_smul ((balanced_iff_neg_mem hc).mpr (fun x hx => hs x hx)) a x

lemma bodyNorm_unit {n : ℕ} {B : Set (Fin n → ℝ)} (hB : IsCompact B) (hc : Convex ℝ B)
    (hs : ∀ x ∈ B, -x ∈ B) (hi : (interior B).Nonempty) :
    (bodyNorm hB hc hs hi).unit = B := by
  ext x
  change gauge B x ≤ 1 ↔ x ∈ B
  rw [gauge_le_one_iff_mem_closure hc (body_nhds_zero hc hs hi),hB.isClosed.closure_eq]

namespace RealNormData
open Finset

lemma dot_continuous {n : ℕ} (p : Fin n → ℝ) : Continuous (fun x : Fin n → ℝ => ∑ i, p i*x i) := by
  fun_prop

theorem isDual_of_polar {n : ℕ} (g h : RealNormData (Fin n → ℝ))
    (hpolar : coordinatePolar g.unit = h.unit) : g.IsDual h := by
  have hupper (p x : Fin n → ℝ) : (∑ i, p i*x i) ≤ g x * h p := by
    by_cases hp : p = 0
    · simp [hp]
    by_cases hx : x = 0
    · simp [hx]
    have hpp : 0 < h p := lt_of_le_of_ne (h.nonneg _) (Ne.symm (h.eq_zero.not.mpr hp))
    have hxx : 0 < g x := lt_of_le_of_ne (g.nonneg _) (Ne.symm (g.eq_zero.not.mpr hx))
    have hpu : (h p)⁻¹ • p ∈ coordinatePolar g.unit := by
      rw [hpolar]
      change h ((h p)⁻¹ • p) ≤ 1
      rw [h.smul_eq,abs_of_pos (inv_pos.mpr hpp),inv_mul_cancel₀ hpp.ne']
    have hxu : (g x)⁻¹ • x ∈ g.unit := by
      change g ((g x)⁻¹ • x) ≤ 1
      rw [g.smul_eq,abs_of_pos (inv_pos.mpr hxx),inv_mul_cancel₀ hxx.ne']
    have hb := hpu _ hxu
    have hb' : (h p)⁻¹ * (g x)⁻¹ * (∑ i, p i*x i) ≤ 1 := by
      have he : (∑ i, ((h p)⁻¹ • p) i * ((g x)⁻¹ • x) i) =
          (h p)⁻¹ * (g x)⁻¹ * (∑ i, p i*x i) := by
        simp only [Pi.smul_apply,smul_eq_mul, mul_sum]
        apply sum_congr rfl
        intro i hi
        ring
      rwa [he] at hb
    have ht := mul_le_mul_of_nonneg_left hb' (mul_nonneg hpp.le hxx.le)
    field_simp at ht
    nlinarith
  refine ⟨fun x p => hupper p x,?_⟩
  intro p
  obtain ⟨x,hx,hmax⟩ := g.isCompact_unit.exists_isMaxOn
    (show g.unit.Nonempty from ⟨0,by simp [unit]⟩) (dot_continuous p).continuousOn
  let t : ℝ := ∑ i, p i*x i
  have ht0 : 0 ≤ t := by
    have hh := hmax (show (0:Fin n → ℝ) ∈ g.unit by simp [unit])
    change (∑ i, p i*(0:Fin n → ℝ) i) ≤ t at hh
    simpa only [Pi.zero_apply,mul_zero,sum_const_zero] using hh
  have htt : t ≤ h p := by
    exact (hupper p x).trans ((mul_le_mul_of_nonneg_right hx (h.nonneg _)).trans_eq (one_mul _))
  have hpt : h p ≤ t := by
    by_contra hnot
    have hlt : t < h p := lt_of_not_ge hnot
    let r : ℝ := (t+h p)/2
    have hr : 0 < r := by dsimp [r]; linarith
    have htr : t < r := by dsimp [r]; linarith
    have hrp : r < h p := by dsimp [r]; linarith
    have hpunit : r⁻¹ • p ∈ coordinatePolar g.unit := by
      intro y hy
      have hy' : (∑ i, p i*y i) ≤ t := hmax hy
      simp only [Pi.smul_apply,smul_eq_mul,mul_assoc,← mul_sum]
      exact (inv_mul_le_iff₀ hr).mpr (by linarith)
    rw [hpolar] at hpunit
    change h (r⁻¹ • p) ≤ 1 at hpunit
    rw [h.smul_eq,abs_of_pos (inv_pos.mpr hr)] at hpunit
    have hh := (inv_mul_le_iff₀ hr).mp hpunit
    linarith
  exact ⟨x,hx,le_antisymm htt hpt⟩

end RealNormData

open Set Finset MeasureTheory

lemma coordinatePolar_bipolar {n : ℕ} {B : Set (Fin n → ℝ)}
    (hc : Convex ℝ B) (hclosed : IsClosed B) (hzero : (0:Fin n → ℝ) ∈ B) :
    coordinatePolar (coordinatePolar B) = B := by
  ext x
  constructor
  · intro hx
    by_contra hnot
    obtain ⟨p,hp,hpx⟩ := exists_coordinatePolar_separator hc hclosed hzero hnot
    have hle := hx p hp
    have he : (∑ i, x i*p i) = ∑ i, p i*x i := by apply sum_congr rfl; intro i hi; ring
    rw [he] at hle
    linarith
  · intro hx p hp
    simpa only [mul_comm] using hp x hx

namespace RealNormData
lemma IsDual.symm {n : ℕ} {g h : RealNormData (Fin n → ℝ)} (hd : g.IsDual h) : h.IsDual g := by
  apply h.isDual_of_polar g
  rw [← hd.polar_unit,coordinatePolar_bipolar g.convex_unit g.isCompact_unit.isClosed g.zero_mem_unit]

lemma coordinate_of_dual {n : ℕ} {g h : RealNormData (Fin n → ℝ)} (hd : g.IsDual h)
    (f : h.Space →L[ℝ] ℝ) :
    ∃ u : Fin n → ℝ, g u ≤ ‖f‖ ∧ ∀ p : h.Space,
      f p = ∑ i, (h.spaceEquiv p) i * u i := by
  let F : (Fin n → ℝ) →L[ℝ] ℝ :=
    f.comp h.spaceEquiv.symm.toContinuousLinearEquiv.toContinuousLinearMap
  let u : Fin n → ℝ := fun i => F (Pi.single i 1)
  have he (p : h.Space) : f p = ∑ i, (h.spaceEquiv p) i*u i := by
    have hh := pairing_of_dual F (h.spaceEquiv p)
    change (∑ i, u i * (h.spaceEquiv p) i) = f (h.spaceEquiv.symm (h.spaceEquiv p)) at hh
    rw [LinearEquiv.symm_apply_apply] at hh
    simpa only [mul_comm] using hh.symm
  refine ⟨u,?_,he⟩
  obtain ⟨p,hp,hpu⟩ := hd.symm.2 u
  have hn : ‖h.spaceEquiv.symm p‖ ≤ 1 := by simpa only [space_norm,LinearEquiv.apply_symm_apply,unit,Set.mem_ofPred_eq] using hp
  have hh := (le_abs_self (f (h.spaceEquiv.symm p))).trans ((f.le_opNorm _).trans
    ((mul_le_mul_of_nonneg_left hn (norm_nonneg f)).trans_eq (mul_one _)))
  rw [he] at hh
  simp only [LinearEquiv.apply_symm_apply] at hh
  rw [← hpu]
  simpa only [mul_comm] using hh

lemma equality_segment_lift {n : ℕ} (hn : 0 < n)
    {g h : RealNormData (Fin n → ℝ)} (hd : g.IsDual h)
    (heq : (volume g.unit).toReal * (volume h.unit).toReal = (4:ℝ)^n/Nat.factorial n) :
    let c := interval 1 (by norm_num : (0:ℝ) < 1)
    (g.coordSum c).IsDual (h.coordMax c) ∧
      (volume (g.coordSum c).unit).toReal * (volume (h.coordMax c).unit).toReal =
        (4:ℝ)^(n+1)/Nat.factorial (n+1) := by
  intro c
  have hc : c.IsDual c := by simpa only [inv_one] using interval_isDual 1 (by norm_num)
  refine ⟨hd.coordSum_max hc,?_⟩
  rw [volumeReal_unit_coordSum hn (by norm_num),volumeReal_unit_coordMax,volumeReal_unit_interval]
  have heq' : (volume h.unit).toReal * (volume g.unit).toReal = (4:ℝ)^n/Nat.factorial n := by
    simpa only [mul_comm] using heq
  have hh := hanner_volume_recursion heq' (show (2:ℝ)*(2:ℝ)=(4:ℝ)^1/Nat.factorial 1 by norm_num)
  convert hh using 1 ; ring

end RealNormData

end SymmetricMahler

end

end OAI
