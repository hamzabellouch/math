import Mathlib
import OAI.Probability.ParisiFinite.MaskedDisorder

namespace OAI

/-! Used Vertices. -/

noncomputable section

open scoped BigOperators ComplexConjugate InnerProductSpace Topology ComplexOrder
open Filter
open scoped BigOperators
open scoped Matrix Matrix.Norms.L2Operator ComplexConjugate
open scoped InnerProductSpace ComplexConjugate
open Filter Topology
open Filter Set Topology
open scoped InnerProductSpace ComplexConjugate Topology
open scoped InnerProductSpace
open scoped BigOperators Topology InnerProductSpace
open scoped BigOperators InnerProductSpace
open scoped BigOperators Matrix Topology ComplexConjugate
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
open scoped BigOperators Matrix Topology
open scoped BigOperators Matrix Topology Matrix.Norms.Operator
open scoped BigOperators Matrix Topology ComplexConjugate
open MeasureTheory ProbabilityTheory Filter

namespace SKQAOA.SiteHistories
variable {n : ℕ}

def usedVertices (r : Edge n) (H : Finset (Edge n)) : Finset (Fin n) :=
  (H∪{r}).biUnion (fun e => {e.1.1,e.1.2})

lemma fst_mem_usedVertices (r : Edge n) (H : Finset (Edge n)) {e : Edge n}
    (he : e∈H∪{r}) : e.1.1∈usedVertices r H :=
  Finset.mem_biUnion.mpr ⟨e,he,by simp⟩

lemma snd_mem_usedVertices (r : Edge n) (H : Finset (Edge n)) {e : Edge n}
    (he : e∈H∪{r}) : e.1.2∈usedVertices r H :=
  Finset.mem_biUnion.mpr ⟨e,he,by simp⟩

lemma card_usedVertices_le (r : Edge n) (H : Finset (Edge n)) :
    (usedVertices r H).card ≤ 2*H.card+2 := by
  calc
    _ ≤ ∑e∈H∪{r}, ({e.1.1,e.1.2}:Finset (Fin n)).card := Finset.card_biUnion_le
    _ ≤ ∑e∈H∪{r}, 2 := by
      apply Finset.sum_le_sum
      intro e he
      exact (Finset.card_insert_le _ _).trans (by simp)
    _ ≤ 2*H.card+2 := by
      simp only [Finset.sum_const,smul_eq_mul]
      have h := Finset.card_union_le H ({r}:Finset (Edge n))
      simp only [Finset.card_singleton] at h
      omega

lemma rootFactor_local (p : ℕ) (γ : Fin p → ℝ) (r : Edge n)
    (H : Finset (Edge n)) (a b : Fin n → Site p)
    (hab : ∀i∈usedVertices r H, a i=b i) : rootFactor p γ r a=rootFactor p γ r b := by
  unfold rootFactor
  rw [hab _ (fst_mem_usedVertices r H (by simp)),hab _ (snd_mem_usedVertices r H (by simp))]

lemma cluster_integrand_local (p : ℕ) (γ : Fin p → ℝ) (r : Edge n)
    (H : Finset (Edge n)) (a b : Fin n → Site p)
    (hab : ∀i∈usedVertices r H, a i=b i) :
    rootFactor p γ r a*(∏e∈H,(factor p γ r a e-1))=
      rootFactor p γ r b*(∏e∈H,(factor p γ r b e-1)) := by
  rw [rootFactor_local p γ r H a b hab]
  congr 1
  apply Finset.prod_congr rfl
  intro e he
  unfold factor
  rw [hab _ (fst_mem_usedVertices r H (Finset.mem_union_left _ he)),
      hab _ (snd_mem_usedVertices r H (Finset.mem_union_left _ he))]

lemma norm_rootFactor_le (p : ℕ) (γ : Fin p → ℝ) (r : Edge n) (a : Fin n → Site p) :
    ‖rootFactor p γ r a‖ ≤ (2*angleMass p γ)*(Real.sqrt (n:ℝ))⁻¹ := by
  have hD := angleMass_nonneg p γ
  simp only [rootFactor,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_bitSpin,
    Complex.norm_I,one_mul,abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_pos (edgeKernel_pos _ _ _ _ _)]
  calc
    _ ≤ (Real.sqrt (n:ℝ))⁻¹*(2*angleMass p γ)*1 := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (abs_delta_le _ _ _ _) (by positivity)
      · exact edgeKernel_le_one _ _ _ _ _
      · exact le_of_lt (edgeKernel_pos _ _ _ _ _)
      · positivity
    _ = _ := by ring

lemma norm_factor_sub_one_le (p : ℕ) (γ : Fin p → ℝ) (r : Edge n)
    (a : Fin n → Site p) (e : Edge n) :
    ‖factor p γ r a e-1‖ ≤ (2*angleMass p γ)^2*((n:ℝ)⁻¹)/2 := by
  by_cases he : e=r
  · simp only [factor,he,ite_true,sub_self,norm_zero]
    positivity
  · simp only [factor,he,ite_false,←Complex.ofReal_one,←Complex.ofReal_sub,
      Complex.norm_real,Real.norm_eq_abs]
    exact abs_edgeKernel_sub_one_le _ _ _ _ _

 
theorem norm_cluster_le_local (p : ℕ) (γ β : Fin p → ℝ) (r : Edge n)
    (H : Finset (Edge n)) :
    ‖cluster p γ β r H‖ ≤ (∑s:Site p,‖weight p β s‖)^(usedVertices r H).card *
      ((2*angleMass p γ)*(Real.sqrt (n:ℝ))⁻¹ *
        ((2*angleMass p γ)^2*((n:ℝ)⁻¹)/2)^H.card) := by
  have hD := angleMass_nonneg p γ
  apply FiniteHistory.norm_expectation_le_of_local (weight p β) (sum_weight p β)
    (usedVertices r H) _ (cluster_integrand_local p γ r H)
  · positivity
  · intro a
    rw [norm_mul,norm_prod]
    apply mul_le_mul (norm_rootFactor_le p γ r a)
    · calc
        _ ≤ ∏e∈H,((2*angleMass p γ)^2*((n:ℝ)⁻¹)/2) :=
          Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun _ _ => norm_factor_sub_one_le _ _ _ _ _)
        _ = _ := by rw [Finset.prod_const]
    · exact Finset.prod_nonneg fun _ _ => norm_nonneg _
    · positivity

 
def variation (p : ℕ) (β : Fin p → ℝ) : ℝ := 1+∑s:Site p,‖weight p β s‖

lemma one_le_variation (p : ℕ) (β : Fin p → ℝ) : 1≤variation p β := by
  unfold variation
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => norm_nonneg _)

def activity (p : ℕ) (γ β : Fin p → ℝ) : ℝ :=
  (variation p β)^2*(2*angleMass p γ)^2/2

def markedBound (p : ℕ) (γ β : Fin p → ℝ) : ℝ :=
  (variation p β)^2*(2*angleMass p γ)

lemma activity_nonneg (p : ℕ) (γ β : Fin p → ℝ) : 0≤activity p γ β := by
  unfold activity
  positivity

lemma markedBound_nonneg (p : ℕ) (γ β : Fin p → ℝ) : 0 ≤ markedBound p γ β := by
  unfold markedBound
  exact mul_nonneg (sq_nonneg _) (mul_nonneg (by norm_num) (angleMass_nonneg p γ))

 

theorem norm_cluster_le (p : ℕ) (γ β : Fin p → ℝ) (r : Edge n)
    (H : Finset (Edge n)) :
    ‖cluster p γ β r H‖ ≤ markedBound p γ β*(Real.sqrt (n:ℝ))⁻¹ *
      (activity p γ β/(n:ℝ))^H.card := by
  have hD := angleMass_nonneg p γ
  have hV : 0≤variation p β := (by norm_num : (0:ℝ)≤1).trans (one_le_variation p β)
  have hW : 0≤∑s:Site p,‖weight p β s‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
  calc
    _ ≤ (∑s:Site p,‖weight p β s‖)^(usedVertices r H).card *
      ((2*angleMass p γ)*(Real.sqrt (n:ℝ))⁻¹ *
        ((2*angleMass p γ)^2*((n:ℝ)⁻¹)/2)^H.card) := norm_cluster_le_local p γ β r H
    _ ≤ (variation p β)^(2*H.card+2) *
      ((2*angleMass p γ)*(Real.sqrt (n:ℝ))⁻¹ *
        ((2*angleMass p γ)^2*((n:ℝ)⁻¹)/2)^H.card) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact (pow_le_pow_left₀ hW (show (∑s:Site p,‖weight p β s‖) ≤ variation p β by
          unfold variation; linarith) _).trans
        (pow_le_pow_right₀ (one_le_variation p β) (card_usedVertices_le r H))
    _ = _ := by
      simp only [markedBound,activity,pow_add,pow_mul,mul_pow,div_eq_mul_inv]
      ring

end SKQAOA.SiteHistories

 

open scoped BigOperators

namespace SKQAOA.SiteHistories
variable {m n N p : ℕ}

 
def edgeMap (f : Fin m ↪o Fin n) : Edge m ↪ Edge n where
  toFun e := ⟨(f e.1.1,f e.1.2),f.strictMono e.2⟩
  inj' := by
    intro e e' h
    apply Subtype.ext
    exact Prod.ext (f.injective (congrArg (fun z : Edge n => z.1.1) h))
      (f.injective (congrArg (fun z : Edge n => z.1.2) h))

@[simp] lemma edgeMap_fst (f : Fin m ↪o Fin n) (e : Edge m) :
    (edgeMap f e).1.1=f e.1.1 := rfl
@[simp] lemma edgeMap_snd (f : Fin m ↪o Fin n) (e : Edge m) :
    (edgeMap f e).1.2=f e.1.2 := rfl

lemma usedVertices_map (f : Fin m ↪o Fin n) (r : Edge m) (H : Finset (Edge m)) :
    usedVertices (edgeMap f r) (H.map (edgeMap f))=(usedVertices r H).map f.toEmbedding := by
  classical
  have hu : H.map (edgeMap f)∪{edgeMap f r}=(H∪{r}).map (edgeMap f) := by simp
  unfold usedVertices
  rw [hu]
  simp only [Finset.map_eq_image,Finset.biUnion_image,Finset.image_biUnion]
  apply Finset.biUnion_congr rfl
  intro e he
  simp only [edgeMap_fst,edgeMap_snd,Finset.image_insert,Finset.image_singleton]
  rfl

 

theorem graphCoefficient_relabel (N p : ℕ) (γ β : Fin p → ℝ)
    (f : Fin m ↪o Fin n) (r : Edge m) (H : Finset (Edge m)) :
    graphCoefficient N n p γ β (edgeMap f r) (H.map (edgeMap f))=
      graphCoefficient N m p γ β r H := by
  unfold graphCoefficient
  have he (a : Fin n → Site p) :
      (∏e∈H.map (edgeMap f),if e=edgeMap f r then (0:ℂ) else
        (kernelScaled N p γ (a e.1.1) (a e.1.2):ℂ))=
      ∏e∈H,if e=r then (0:ℂ) else
        (kernelScaled N p γ ((a ∘ f) e.1.1) ((a ∘ f) e.1.2):ℂ) := by
    simp only [Finset.prod_map,Function.Embedding.apply_eq_iff_eq,edgeMap_fst,edgeMap_snd,Function.comp_def]
  simp_rw [he]
  exact FiniteHistory.expectation_embedding (weight p β) (sum_weight p β) f.toEmbedding
    (fun a : Fin m → Site p =>
      (bitSpin (a r.1.1).1:ℂ)*(bitSpin (a r.1.2).1:ℂ)*Complex.I*
        (delta p γ (a r.1.1) (a r.1.2):ℂ)*
        (edgeKernel N p γ (a r.1.1) (a r.1.2):ℂ)*
          ∏e∈H,if e=r then 0 else (kernelScaled N p γ (a e.1.1) (a e.1.2):ℂ))

def rawGraphCoefficient (N m p : ℕ) (γ β : Fin p → ℝ) (r : Edge m)
    (H : Finset (Edge m)) : ℂ :=
  FiniteHistory.expectation (weight p β) (fun a : Fin m → Site p =>
    (bitSpin (a r.1.1).1:ℂ)*(bitSpin (a r.1.2).1:ℂ)*Complex.I*
      (delta p γ (a r.1.1) (a r.1.2):ℂ)*
      (edgeKernel N p γ (a r.1.1) (a r.1.2):ℂ)*
        ∏e∈H,if e=r then 0 else ((edgeKernel N p γ (a e.1.1) (a e.1.2):ℂ)-1))

lemma graphCoefficient_eq_pow_mul_raw (N m p : ℕ) (γ β : Fin p → ℝ) (r : Edge m)
    (H : Finset (Edge m)) :
    graphCoefficient N m p γ β r H=(N:ℂ)^H.card*rawGraphCoefficient N m p γ β r H := by
  unfold graphCoefficient rawGraphCoefficient FiniteHistory.expectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have he (e : Edge m) : (if e=r then (0:ℂ) else (kernelScaled N p γ (a e.1.1) (a e.1.2):ℂ))=
      (N:ℂ)*(if e=r then (0:ℂ) else (edgeKernel N p γ (a e.1.1) (a e.1.2):ℂ)-1) := by
    split_ifs <;> simp [kernelScaled]
  simp_rw [he]
  rw [Finset.prod_mul_distrib,Finset.prod_const]
  ring

lemma cluster_eq_inv_sqrt_mul_raw (p : ℕ) (γ β : Fin p → ℝ) (r : Edge n)
    (H : Finset (Edge n)) :
    cluster p γ β r H=((Real.sqrt (n:ℝ))⁻¹:ℂ)*rawGraphCoefficient n n p γ β r H := by
  unfold cluster rawGraphCoefficient FiniteHistory.expectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  have he (e : Edge n) : factor p γ r a e-1=
      if e=r then (0:ℂ) else (edgeKernel n p γ (a e.1.1) (a e.1.2):ℂ)-1 := by
    split_ifs with h <;> simp [factor,h]
  simp_rw [he]
  unfold rootFactor
  ring

lemma cluster_eq_scaled (p : ℕ) (γ β : Fin p → ℝ) (r : Edge n)
    (H : Finset (Edge n)) :
    cluster p γ β r H=((Real.sqrt (n:ℝ))⁻¹:ℂ)*
      (n:ℂ)⁻¹^H.card*graphCoefficient n n p γ β r H := by
  have hn : n≠0 := Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le _) r.1.2.isLt)
  have hnC : (n:ℂ)≠0 := Nat.cast_ne_zero.mpr hn
  rw [cluster_eq_inv_sqrt_mul_raw,graphCoefficient_eq_pow_mul_raw]
  rw [←mul_assoc, mul_assoc ((Real.sqrt (n:ℝ))⁻¹:ℂ),←mul_pow,inv_mul_cancel₀ hnC,one_pow,mul_one]

end SKQAOA.SiteHistories

 

open scoped BigOperators

namespace SKQAOA.SiteHistories
attribute [local instance] Classical.propDecidable
variable {m n : ℕ}

abbrev MarkedGraph (n : ℕ) := Edge n × Finset (Edge n)
abbrev FullGraph (m : ℕ) := {g : MarkedGraph m // usedVertices g.1 g.2=Finset.univ}
abbrev SupportSet (n m : ℕ) := {U : Finset (Fin n) // U.card=m}

def graphMap (f : Fin m ↪o Fin n) (g : MarkedGraph m) : MarkedGraph n :=
  (edgeMap f g.1,g.2.map (edgeMap f))

lemma graphMap_injective (f : Fin m ↪o Fin n) : Function.Injective (graphMap f) := by
  intro g h he
  apply Prod.ext
  · exact (edgeMap f).injective (congrArg Prod.fst he)
  · exact Finset.map_injective (edgeMap f) (congrArg Prod.snd he)

lemma graphMap_support (f : Fin m ↪o Fin n) (g : MarkedGraph m) :
    usedVertices (graphMap f g).1 (graphMap f g).2=(usedVertices g.1 g.2).map f.toEmbedding :=
  usedVertices_map f g.1 g.2

lemma edgeMap_surjective_on (U : SupportSet n m) (e : Edge n)
    (h₁ : e.1.1∈U.1) (h₂ : e.1.2∈U.1) :
    ∃d : Edge m,edgeMap (U.1.orderEmbOfFin U.2) d=e := by
  let i : Fin m := (U.1.orderIsoOfFin U.2).symm ⟨e.1.1,h₁⟩
  let j : Fin m := (U.1.orderIsoOfFin U.2).symm ⟨e.1.2,h₂⟩
  have hi : U.1.orderEmbOfFin U.2 i=e.1.1 := by
    exact congrArg Subtype.val ((U.1.orderIsoOfFin U.2).apply_symm_apply ⟨e.1.1,h₁⟩)
  have hj : U.1.orderEmbOfFin U.2 j=e.1.2 := by
    exact congrArg Subtype.val ((U.1.orderIsoOfFin U.2).apply_symm_apply ⟨e.1.2,h₂⟩)
  have hij : i<j := by
    apply (U.1.orderEmbOfFin U.2).lt_iff_lt.mp
    simpa only [hi,hj] using e.2
  exact ⟨⟨(i,j),hij⟩,Subtype.ext (Prod.ext hi hj)⟩

lemma graphMap_surjective_on (U : SupportSet n m) (g : MarkedGraph n)
    (hg : usedVertices g.1 g.2=U.1) :
    ∃h : FullGraph m,graphMap (U.1.orderEmbOfFin U.2) h.1=g := by
  let f := U.1.orderEmbOfFin U.2
  have hr : ∃r : Edge m,edgeMap f r=g.1 := edgeMap_surjective_on U g.1
    (hg ▸ fst_mem_usedVertices g.1 g.2 (by simp))
    (hg ▸ snd_mem_usedVertices g.1 g.2 (by simp))
  obtain ⟨r,hr⟩ := hr
  let H : Finset (Edge m) := Finset.univ.filter (fun e => edgeMap f e∈g.2)
  have hH : H.map (edgeMap f)=g.2 := by
    ext e
    constructor
    · intro he
      obtain ⟨d,hd,rfl⟩ := Finset.mem_map.mp he
      exact (Finset.mem_filter.mp hd).2
    · intro he
      obtain ⟨d,hd⟩ := edgeMap_surjective_on U e
        (hg ▸ fst_mem_usedVertices g.1 g.2 (Finset.mem_union_left _ he))
        (hg ▸ snd_mem_usedVertices g.1 g.2 (Finset.mem_union_left _ he))
      exact Finset.mem_map.mpr ⟨d,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hd ▸ he⟩,hd⟩
  have hs : usedVertices r H=Finset.univ := by
    apply Finset.map_injective f.toEmbedding
    rw [←usedVertices_map,hr,hH,hg]
    exact (Finset.map_orderEmbOfFin_univ U.1 U.2).symm
  exact ⟨⟨(r,H),hs⟩,Prod.ext hr hH⟩

 

def embedFullGraph (z : SupportSet n m × FullGraph m) :
    {g : MarkedGraph n // (usedVertices g.1 g.2).card=m} :=
  ⟨graphMap (z.1.1.orderEmbOfFin z.1.2) z.2.1,by
    rw [graphMap_support,z.2.2,Finset.map_orderEmbOfFin_univ]
    exact z.1.2⟩

lemma embedFullGraph_support (z : SupportSet n m × FullGraph m) :
    usedVertices (embedFullGraph z).1.1 (embedFullGraph z).1.2=z.1.1 := by
  change usedVertices (graphMap _ _).1 (graphMap _ _).2=_
  rw [graphMap_support,z.2.2,Finset.map_orderEmbOfFin_univ]

lemma embedFullGraph_bijective : Function.Bijective (embedFullGraph (n := n) (m := m)) := by
  constructor
  · rintro ⟨U,g⟩ ⟨V,h⟩ he
    have hU : U=V := by
      apply Subtype.ext
      rw [←embedFullGraph_support (U,g),←embedFullGraph_support (V,h),he]
    subst V
    have hgh : g=h := Subtype.ext (graphMap_injective (U.1.orderEmbOfFin U.2)
      (congrArg Subtype.val he))
    exact Prod.ext rfl hgh
  · intro g
    let U : SupportSet n m := ⟨usedVertices g.1.1 g.1.2,g.2⟩
    obtain ⟨h,hh⟩ := graphMap_surjective_on U g.1 rfl
    exact ⟨(U,h),Subtype.ext hh⟩

def supportGraphEquiv (n m : ℕ) : SupportSet n m × FullGraph m ≃
    {g : MarkedGraph n // (usedVertices g.1 g.2).card=m} :=
  Equiv.ofBijective embedFullGraph embedFullGraph_bijective

lemma card_supportSet (n m : ℕ) : Fintype.card (SupportSet n m)=n.choose m := by
  have he : (Finset.univ.filter (fun U : Finset (Fin n) => U.card=m))=
      Finset.univ.powersetCard m := by
    ext U
    simp
  rw [Fintype.card_subtype,he,Finset.card_powersetCard,Finset.card_univ,Fintype.card_fin]

 

theorem sum_full_graphs {R : Type*} [AddCommMonoid R]
    (F : MarkedGraph n → R) :
    (∑g : MarkedGraph n with (usedVertices g.1 g.2).card=m,F g)=
      ∑U : SupportSet n m,∑h : FullGraph m,F (graphMap (U.1.orderEmbOfFin U.2) h.1) := by
  calc
    _ = ∑g : {g : MarkedGraph n // (usedVertices g.1 g.2).card=m},F g.1 :=
      Finset.sum_subtype _ (by simp) F
    _ = ∑z : SupportSet n m × FullGraph m,F ((supportGraphEquiv n m) z).1 :=
      ((supportGraphEquiv n m).sum_comp (fun g => F g.1)).symm
    _ = _ := Fintype.sum_prod_type _

end SKQAOA.SiteHistories

 

open scoped BigOperators Topology

namespace BoundedBranch

 

def Tree (n : ℕ) : ℕ → Type
  | 0 => Unit
  | h+1 => Fin n → Option (Tree n h)

instance treeFintype (n : ℕ) : (h : ℕ) → Fintype (Tree n h)
  | 0 => inferInstanceAs (Fintype Unit)
  | h+1 => letI := treeFintype n h
           inferInstanceAs (Fintype (Fin n → Option (Tree n h)))

def size (n : ℕ) : (h : ℕ) → Tree n h → ℕ
  | 0, _ => 0
  | h+1, b => ∑i, (b i).elim 0 (fun c => 1+size n h c)

def weight (n : ℕ) (x : ℝ) : (h : ℕ) → Tree n h → ℝ
  | 0, _ => 1
  | h+1, b => ∏i, (b i).elim 1 (fun c => (x/(n:ℝ))*weight n x h c)

def partition (n h : ℕ) (x : ℝ) : ℝ := ∑b : Tree n h, weight n x h b

@[simp] theorem partition_zero (n : ℕ) (x : ℝ) : partition n 0 x=1 := by
  change (∑_ : Unit, (1:ℝ))=1
  simp

theorem weight_nonneg (n h : ℕ) {x : ℝ} (hx : 0≤x) (b : Tree n h) :
    0≤weight n x h b := by
  induction h with
  | zero => exact zero_le_one
  | succ h ih =>
    apply Finset.prod_nonneg
    intro i hi
    cases hb : b i with
    | none => exact zero_le_one
    | some c => exact mul_nonneg (div_nonneg hx (Nat.cast_nonneg n)) (ih c)

theorem partition_nonneg (n h : ℕ) {x : ℝ} (hx : 0≤x) : 0≤partition n h x :=
  Finset.sum_nonneg fun b _ => weight_nonneg n h hx b

 
theorem partition_succ (n h : ℕ) (x : ℝ) :
    partition n (h+1) x=(1+x/(n:ℝ)*partition n h x)^n := by
  classical
  change (∑b : Fin n → Option (Tree n h), ∏i,
    (b i).elim 1 (fun c => (x/(n:ℝ))*weight n x h c)) = _
  rw [← Fintype.prod_sum (fun (_ : Fin n) (c : Option (Tree n h)) =>
    c.elim 1 (fun b => (x/(n:ℝ))*weight n x h b))]
  simp [← Finset.mul_sum,partition]

 
def tower (x : ℝ) : ℕ → ℝ
  | 0 => 1
  | h+1 => Real.exp (x*tower x h)

theorem tower_pos (x : ℝ) (h : ℕ) : 0<tower x h := by
  cases h with
  | zero => exact zero_lt_one
  | succ h => exact Real.exp_pos _

theorem partition_step_bound (n h : ℕ) {x : ℝ} (hx : 0≤x) :
    partition n (h+1) x ≤ Real.exp (x*partition n h x) := by
  rw [partition_succ]
  rcases n.eq_zero_or_pos with rfl|hn
  · simp only [pow_zero]
    exact Real.one_le_exp_iff.mpr (mul_nonneg hx (partition_nonneg 0 h hx))
  have hp := partition_nonneg n h hx
  have hnR : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  calc
    (1+x/(n:ℝ)*partition n h x)^n ≤ (Real.exp (x/(n:ℝ)*partition n h x))^n := by
      apply pow_le_pow_left₀ (by positivity)
      simpa only [add_comm] using Real.add_one_le_exp (x/(n:ℝ)*partition n h x)
    _ = Real.exp (x*partition n h x) := by
      rw [←Real.exp_nat_mul]
      congr 1
      field_simp [hnR]

theorem partition_le_tower (n h : ℕ) {x : ℝ} (hx : 0≤x) :
    partition n h x ≤ tower x h := by
  induction h with
  | zero => simp [tower]
  | succ h ih =>
    exact (partition_step_bound n h hx).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ih hx))

theorem weight_eq_pow (n h : ℕ) (x : ℝ) (b : Tree n h) :
    weight n x h b=(x/(n:ℝ))^(size n h b) := by
  induction h with
  | zero => rfl
  | succ h ih =>
    change (∏i, (b i).elim 1 (fun c => (x/(n:ℝ))*weight n x h c)) =
      (x/(n:ℝ))^(∑i, (b i).elim 0 (fun c => 1+size n h c))
    rw [←Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_congr rfl
    intro i hi
    cases hb : b i with
    | none => simp
    | some c => simp [ih,pow_add]

theorem weight_scale (n h : ℕ) (x z : ℝ) (b : Tree n h) :
    weight n (z*x) h b=z^(size n h b)*weight n x h b := by
  simp only [weight_eq_pow,mul_div_assoc,mul_pow]

def tail (n h L : ℕ) (x : ℝ) : ℝ :=
  ∑b : Tree n h with L ≤ size n h b, weight n x h b

 

theorem tail_bound (n h L : ℕ) {x : ℝ} (hx : 0≤x) :
    tail n h L x ≤ tower (2*x) h/(2:ℝ)^L := by
  have htwo : (0:ℝ)<2^L := pow_pos (by norm_num) _
  have hbound : (2:ℝ)^L*tail n h L x ≤ partition n h (2*x) := by
    classical
    unfold tail partition
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑b : Tree n h with L ≤ size n h b, weight n (2*x) h b := by
        apply Finset.sum_le_sum
        intro b hb
        rw [weight_scale]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (by norm_num) (Finset.mem_filter.mp hb).2)
          (weight_nonneg n h hx b)
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun b _ _ => weight_nonneg n h (by positivity) b)
  apply (le_div_iff₀ htwo).mpr
  rw [mul_comm]
  exact hbound.trans (partition_le_tower n h (by positivity))

theorem uniform_tail {h : ℕ} {x ε : ℝ} (hx : 0≤x) (hε : 0<ε) :
    ∃L : ℕ, ∀n : ℕ, tail n h L x<ε := by
  open Filter in
  have ht : Tendsto (fun L : ℕ => tower (2*x) h/(2:ℝ)^L) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (r := (2:ℝ)) (by norm_num))
  obtain ⟨L,hL⟩ := Filter.eventually_atTop.mp (ht.eventually (gt_mem_nhds hε))
  exact ⟨L,fun n => (tail_bound n h L hx).trans_lt (hL L le_rfl)⟩

end BoundedBranch

end

end OAI
