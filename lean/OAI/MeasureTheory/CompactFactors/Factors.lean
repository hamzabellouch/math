import OAI.MeasureTheory.CompactFactors.Functions

namespace OAI

noncomputable section

open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators BoundedContinuousFunction
open Filter Topology
open MeasureTheory Filter
open scoped ENNReal ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ComplexConjugate
open scoped BigOperators
open scoped BigOperators
open Polynomial
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators
open MeasureTheory
open MeasureTheory ProbabilityTheory
open scoped BigOperators
open MeasureTheory
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
open MeasureTheory Filter
open scoped Topology ENNReal NNReal
open MeasureTheory
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace EuclideanFiveColor
open MeasureTheory
structure OrbitSpace (K : Type*) where
  val : K → ℂ

namespace OrbitSpace
variable {K : Type*}
def equiv (K : Type*) : OrbitSpace K ≃ (K → ℂ) where
  toFun := val
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl

instance : Inhabited (OrbitSpace K) := ⟨⟨fun _ => 0⟩⟩
instance : TopologicalSpace (OrbitSpace K) := (equiv K).topologicalSpace
instance : MeasurableSpace (OrbitSpace K) := borel _
instance : BorelSpace (OrbitSpace K) := ⟨rfl⟩
instance [Countable K] : PolishSpace (OrbitSpace K) := (equiv K).polishSpace_induced

@[ext] lemma ext {a b : OrbitSpace K} (h : ∀ k, a.val k = b.val k) : a = b := by
  cases a; cases b; congr; funext k; exact h k

lemma continuous_val : Continuous (val : OrbitSpace K → K → ℂ) :=
  (equiv K).homeomorph.continuous
lemma continuous_mk : Continuous (mk : (K → ℂ) → OrbitSpace K) :=
  (equiv K).homeomorph.symm.continuous
lemma measurable_val [Countable K] : Measurable (val : OrbitSpace K → K → ℂ) := continuous_val.measurable
lemma measurable_mk [Countable K] : Measurable (mk : (K → ℂ) → OrbitSpace K) := continuous_mk.measurable

instance [Monoid K] : MulAction K (OrbitSpace K) where
  smul k f := ⟨fun l => f.val (l*k)⟩
  one_smul f := by ext l; exact congrArg f.val (mul_one l)
  mul_smul a b f := by ext l; exact congrArg f.val (mul_assoc l a b).symm

@[simp] lemma smul_val [Monoid K] (k : K) (f : OrbitSpace K) (l : K) :
    (k • f).val l = f.val (l*k) := rfl

instance [Monoid K] : ContinuousConstSMul K (OrbitSpace K) where
  continuous_const_smul k := continuous_mk.comp
    (continuous_pi fun l => (continuous_apply (l*k)).comp continuous_val)
instance [Monoid K] : MeasurableConstSMul K (OrbitSpace K) where
  measurable_const_smul k := (continuous_const_smul k).measurable

end OrbitSpace

namespace OrbitFactor
variable {K X Y : Type*} [Monoid K] [MulAction K X] [MulAction K Y]
  [MeasurableSpace X] [MeasurableSpace Y]

def orbit (H : X → ℂ) (x : X) : OrbitSpace K := ⟨fun k => H (k • x)⟩

omit [MulAction K Y] [MeasurableSpace Y] in
lemma measurable_orbit [Countable K] [MeasurableConstSMul K X]
    {H : X → ℂ} (hH : Measurable H) : Measurable (orbit (K := K) H) :=
  OrbitSpace.measurable_mk.comp (Measurable.of_eval fun k => hH.comp (measurable_const_smul k))

omit [MulAction K Y] [MeasurableSpace X] [MeasurableSpace Y] in
lemma orbit_equivariant (H : X → ℂ) (k : K) (x : X) :
    orbit (K := K) H (k • x) = k • orbit H x := by
  ext l
  exact congrArg H (mul_smul l k x).symm

def extend (q : X → Y) (H : X → ℂ) (x : X) : Y × OrbitSpace K := (q x, orbit H x)

omit [MulAction K Y] in
lemma measurable_extend [Countable K] [MeasurableConstSMul K X]
    {q : X → Y} (hq : Measurable q) {H : X → ℂ} (hH : Measurable H) :
    Measurable (extend (K := K) q H) := hq.prodMk (measurable_orbit hH)

omit [MeasurableSpace Y] in
lemma extend_equivariant (μ : Measure X) {q : X → Y} (H : X → ℂ)
    (hqcov : ∀ k : K, ∀ᵐ x ∂μ, q (k • x) = k • q x) (k : K) :
    ∀ᵐ x ∂μ, extend (K := K) q H (k • x) = k • extend q H x := by
  filter_upwards [hqcov k] with x hx
  exact Prod.ext hx (orbit_equivariant H k x)

omit [MeasurableSpace X] in
@[simp] lemma orbit_one (H : X → ℂ) (x : X) : (orbit (K := K) H x).val 1 = H x := by
  simp only [orbit, one_smul]

end OrbitFactor
end EuclideanFiveColor

namespace EuclideanFiveColor.OrbitFactor
open MeasureTheory ProbabilityTheory CompactFunctions
variable {K X Y : Type*} [Monoid K] [Countable K] [MulAction K X] [MulAction K Y]
  [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
  [MeasurableConstSMul K X] [MeasurableConstSMul K Y]

omit [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y] in
lemma measurable_extend_compactSigma (μ : Measure X) [IsProbabilityMeasure μ]
    (q : X → Y) (hq : Measurable q)
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k • x) μ μ)
    (hqcov : ∀ k : K, ∀ᵐ x ∂μ, q (k • x) = k • q x)
    (H : X → ℂ) (hH : Measurable H) (hc : Compact (K := K) μ q H) :
    @Measurable X (Y × OrbitSpace K) (compactSigma μ q hq hpres) inferInstance
      (extend (K := K) q H) := by
  have hHm := measurable_compactSigma hq hpres hH hc
  have hpm : @Measurable X (K → ℂ) (compactSigma μ q hq hpres) inferInstance
      (fun x k => H (k • x)) :=
    @Measurable.of_eval X K (fun _ => ℂ) (compactSigma μ q hq hpres) (fun _ => inferInstance) _ (fun k => hHm.comp (measurable_shift_compactSigma hq hpres k))
  exact (measurable_base_compactSigma hq hpres hqcov).prodMk
    (OrbitSpace.measurable_mk.comp hpm)

/-- The orbit factor generated by a compact scalar function is an actual
compact extension; the finite module is projected onto that factor. -/
lemma compact_orbit_extension (μ : Measure X) [IsProbabilityMeasure μ]
    (q : X → Y) (hq : Measurable q)
    (hpres : ∀ k : K, MeasurePreserving (fun x : X => k • x) μ μ)
    (hqcov : ∀ k : K, ∀ᵐ x ∂μ, q (k • x) = k • q x)
    (H : X → ℂ) (hH : Measurable H) (hc : Compact (K := K) μ q H)
    (F : Y × OrbitSpace K → ℂ) (hF : Measurable F)
    (D : ℝ) (hD : 0 ≤ D) (hFD : ∀ z, ‖F z‖ ≤ D) :
    Compact (K := K) (μ.map (extend (K := K) q H)) Prod.fst F := by
  let : MeasurableConstSMul K (Y × OrbitSpace K) := ⟨fun k =>
    ((measurable_const_smul k).comp measurable_fst).prodMk
      ((measurable_const_smul k).comp measurable_snd)⟩
  apply compact_descend μ (extend (K := K) q H) (measurable_extend hq hH)
    Prod.fst measurable_fst (extend_equivariant μ H hqcov) F hF D hD hFD
  change Compact (K := K) μ q (F ∘ extend (K := K) q H)
  exact compact_of_measurable_compactSigma hq hpres
    (hF.comp (measurable_extend_compactSigma μ q hq hpres hqcov H hH hc)) D hD
    (fun x => hFD _)

end EuclideanFiveColor.OrbitFactor
namespace EuclideanFiveColor.KernelCompact
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {K X Y : Type*} [Group K] [MulAction K X] [MulAction K Y]
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace.CountablyGenerated X]
  [MeasurableConstSMul K X] [MeasurableConstSMul K Y]

omit [MeasurableConstSMul K Y] in
lemma compact_applyKernel (μ : Measure X) [IsProbabilityMeasure μ]
    (κ : Kernel Y X) [IsMarkovKernel κ] (q : X → Y) (hq : Measurable q)
    (L : X × X → ℂ) (hL : Measurable L) (C : ℝ) (hC : 0 ≤ C)
    (hLC : ∀ z, ‖L z‖ ≤ C)
    (hqcov : ∀ k : K, ∀ᵐ x ∂μ, q (k • x) = k • q x)
    (hκcov : ∀ k : K, ∀ᵐ y ∂μ.map q, κ (k • y) = (κ y).map (fun x => k • x))
    (hLcov : ∀ k : K, ∀ᵐ z ∂μ ⊗ₘ κ.comap q hq, L (k • z.1, k • z.2) = L z)
    (f : X → ℂ) (hfm : Measurable f) (hfB : ∀ x, ‖f x‖ ≤ 1) :
    CompactFunctions.Compact (K := K) μ q (applyKernel κ q L f) := by
  intro ε hε
  obtain ⟨r, B, C₀, Hf, hB, hC₀, hHm, hHb, ha⟩ :=
    bounded_range_approximation μ κ q hq L hL C hC hLC ε hε
  refine ⟨r, B, C₀, Hf, hB, hC₀, hHm, hHb, ?_⟩
  intro k
  obtain ⟨a, ham, hab, hai, hae⟩ := ha (fun x => f (k • x))
    (hfm.comp (measurable_const_smul k)) (fun x => hfB (k • x))
  have he := applyKernel_covariance μ κ q hq L hL hqcov hκcov hLcov f hfm k
  have hd : (fun x => dist (applyKernel κ q L f (k • x))
      (∑ i, a (q x) i * Hf i x)^2) =ᵐ[μ]
      (fun x => dist (applyKernel κ q L (fun x => f (k • x)) x)
        (∑ i, a (q x) i * Hf i x)^2) := he.mono fun x hx => by dsimp only at hx ⊢; rw [hx]
  exact ⟨a, ham, hab, hai.congr hd.symm, by rw [integral_congr_ae hd]; exact hae⟩

end EuclideanFiveColor.KernelCompact
namespace EuclideanFiveColor.CompactTower
open MeasureTheory ProbabilityTheory KernelCompact CompactFunctions OrbitFactor
variable {K X Y : Type*} [Group K] [Countable K] [MulAction K X] [MulAction K Y]
  [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [Nonempty X] [StandardBorelSpace Y] [Nonempty Y]
  [MeasurableConstSMul K X] [MeasurableConstSMul K Y]

/-- The strict compact-successor step of the compact tower. The new coordinate
is constructed from a centered invariant conditional-product kernel. -/
theorem strict_compact_successor (μ : Measure X) [IsProbabilityMeasure μ]
    [ErgodicSMul K X μ] (q : X → Y) (hq : Measurable q)
    (hqcov : ∀ k : K, ∀ᵐ x ∂μ, q (k • x) = k • q x)
    (hn : ¬ ErgodicSMul K (X × X) (RelativeProduct.law μ q hq)) :
    ∃ H : X → ℂ, Measurable H ∧ (∀ x, ‖H x‖ ≤ 2) ∧
      (¬ ∃ b : Y → ℂ, Measurable b ∧ H =ᵐ[μ] b ∘ q) ∧
      (∀ F : Y × OrbitSpace K → ℂ, Measurable F →
        (∃ C : ℝ, ∀ z, ‖F z‖ ≤ C) →
        Compact (K := K) (μ.map (extend (K := K) q H)) Prod.fst F) := by
  have hpres (k : K) := measurePreserving_smul k μ
  let κ := condDistrib id q μ
  let : SMulInvariantMeasure K (X × X) (μ ⊗ₘ κ.comap q hq) :=
    RelativeProduct.law_invariant μ q hq hpres hqcov
  have hκcov := RelativeProduct.conditional_covariance μ q hq hpres hqcov
  obtain ⟨L, hLm, hLB, hLcov, hLn, _hrow, hcol⟩ := centered_kernel μ κ q hq
    (RelativeProduct.law_swap μ q hq) hqcov hκcov hn
  obtain ⟨f, hfm, hfB, hfn⟩ := exists_nonzero_image μ κ q hq L hLm 2 (by norm_num) hLB hLn
  let H := applyKernel κ q L f
  have hHm : Measurable H := measurable_applyKernel κ q hq L hLm f hfm
  have hHc : Compact (K := K) μ q H := compact_applyKernel μ κ q hq L hLm 2
    (by norm_num) hLB hqcov hκcov hLcov f hfm hfB
  refine ⟨H, hHm, applyKernel_bound κ q L 2 hLB f hfB, ?_, ?_⟩
  · exact nonzero_not_factorizable μ q hq H hfn
      (image_conditional_mean_zero μ q hq L hLm 2 hLB f hfm hfB hcol)
  · intro F hF hFB
    obtain ⟨C,hC⟩ := hFB
    have hC0 : 0 ≤ C := (norm_nonneg (F (Classical.choice inferInstance))).trans (hC _)
    exact compact_orbit_extension μ q hq hpres hqcov H hHm hHc F hF C hC0 hC

end EuclideanFiveColor.CompactTower

namespace EuclideanFiveColor.FactorCode
open MeasureTheory
variable {K X Y : Type*} [Group K] [Countable K]
  [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace Y]
  [MulAction K X] [MeasurableConstSMul K X]

def scalar (Y : Type*) [MeasurableSpace Y] [StandardBorelSpace Y] (y : Y) : ℂ :=
  Real.arctan (embeddingReal Y y)

lemma scalar_measurable : Measurable (scalar Y) :=
  Complex.measurable_ofReal.comp (Real.continuous_arctan.measurable.comp (measurable_embeddingReal Y))

lemma scalar_injective : Function.Injective (scalar Y) := by
  intro x y h
  apply (measurableEmbedding_embeddingReal Y).injective
  apply Real.arctan_injective
  exact_mod_cast (show (Real.arctan (embeddingReal Y x) : ℂ) = Real.arctan (embeddingReal Y y) from h)

lemma scalar_embedding : MeasurableEmbedding (scalar Y) :=
  scalar_measurable.measurableEmbedding scalar_injective

lemma scalar_bound (y : Y) : ‖scalar Y y‖ ≤ 2 := by
  rw [scalar, Complex.norm_real, Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · have := Real.neg_pi_div_two_lt_arctan (embeddingReal Y y)
    linarith [Real.pi_lt_four]
  · have := Real.arctan_lt_pi_div_two (embeddingReal Y y)
    linarith [Real.pi_lt_four]

def encode (p : X → Y) : X → OrbitSpace K := OrbitFactor.orbit (scalar Y ∘ p)

lemma encode_measurable {p : X → Y} (hp : Measurable p) : Measurable (encode (K := K) p) :=
  OrbitFactor.measurable_orbit (scalar_measurable.comp hp)

omit [Countable K] [MeasurableSpace X] [MeasurableConstSMul K X] in
lemma encode_equivariant (p : X → Y) (k : K) (x : X) :
    encode (K := K) p (k • x) = k • encode (K := K) p x := OrbitFactor.orbit_equivariant _ _ _

omit [Countable K] [MeasurableSpace X] [MeasurableConstSMul K X] in
lemma encode_bound (p : X → Y) (x : X) (k : K) : ‖(encode p x).val k‖ ≤ 2 := scalar_bound _

variable [Nonempty Y]
def decode : OrbitSpace K → Y := fun z => scalar_embedding.invFun (z.val 1)

lemma decode_measurable : Measurable (decode (K := K) (Y := Y)) :=
  scalar_embedding.measurable_invFun.comp ((measurable_pi_apply 1).comp OrbitSpace.measurable_val)

omit [Countable K] [MeasurableSpace X] [MeasurableConstSMul K X] in
lemma decode_encode (p : X → Y) (x : X) : decode (encode (K := K) p x) = p x := by
  dsimp only [decode, encode]
  rw [OrbitFactor.orbit_one]
  exact scalar_embedding.leftInverse_invFun _

omit [Nonempty Y] [MeasurableConstSMul K X] in
lemma encode_as_comp [MulAction K Y] [MeasurableConstSMul K Y]
    (μ : Measure X) (p : X → Y) (hpe : ∀ k : K, ∀ᵐ x ∂μ, p (k • x) = k • p x) :
    ∀ᵐ x ∂μ, encode (K := K) p x = encode (K := K) (id : Y → Y) (p x) := by
  filter_upwards [ae_all_iff.mpr hpe] with x hx
  ext k
  exact congrArg (scalar Y) (hx k)

end EuclideanFiveColor.FactorCode
namespace EuclideanFiveColor.FactorLp
open MeasureTheory
variable {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
  [StandardBorelSpace Y] [Nonempty Y]

def space (μ : Measure X) (p : X → Y) : Submodule ℂ (Lp ℂ 2 μ) :=
  lpMeas ℂ ℂ (MeasurableSpace.comap p inferInstance) 2 μ

omit [StandardBorelSpace Y] [Nonempty Y] in
lemma isClosed (μ : Measure X) {p : X → Y} (hp : Measurable p) :
    IsClosed (space μ p : Set (Lp ℂ 2 μ)) :=
  isClosed_aestronglyMeasurable hp.comap_le

omit [StandardBorelSpace Y] [Nonempty Y] in
lemma exists_rep (μ : Measure X) (p : X → Y) (f : Lp ℂ 2 μ) (hf : f ∈ space μ p) :
    ∃ g : Y → ℂ, Measurable g ∧ (f : X → ℂ) =ᵐ[μ] g ∘ p := by
  obtain ⟨h, hh, hfe⟩ := hf
  obtain ⟨g, hg, he⟩ := hh.measurable.exists_eq_measurable_comp (f := p)
  exact ⟨g, hg, by simpa only [he] using hfe⟩

omit [StandardBorelSpace Y] [Nonempty Y] in
lemma mem_of_rep (μ : Measure X) (p : X → Y) (f : Lp ℂ 2 μ)
    (g : Y → ℂ) (hg : Measurable g) (he : (f : X → ℂ) =ᵐ[μ] g ∘ p) : f ∈ space μ p := by
  exact ⟨g ∘ p, (hg.comp (Measurable.of_comap_le le_rfl)).stronglyMeasurable, he⟩

omit [StandardBorelSpace Y] [Nonempty Y] in
lemma le_of_factor (μ : Measure X) (p : X → Y) (q : X → Z)
    (r : Z → Y) (hr : Measurable r) (he : p =ᵐ[μ] r ∘ q) : space μ p ≤ space μ q := by
  intro f hf
  obtain ⟨g, hg, hfe⟩ := exists_rep μ p f hf
  apply mem_of_rep μ q f (g ∘ r) (hg.comp hr)
  filter_upwards [hfe, he] with x hx he
  simpa only [Function.comp_apply, he] using hx

lemma factor_of_le (μ : Measure X) [IsFiniteMeasure μ]
    (p : X → Y) (q : X → Z) (hp : Measurable p) (hle : space μ p ≤ space μ q) :
    ∃ r : Z → Y, Measurable r ∧ p =ᵐ[μ] r ∘ q := by
  let f := FactorCode.scalar Y ∘ p
  have hfm : Measurable f := FactorCode.scalar_measurable.comp hp
  have hf : MemLp f 2 μ := MemLp.of_bound hfm.aestronglyMeasurable 2
    (Filter.Eventually.of_forall fun x => FactorCode.scalar_bound (p x))
  have hmem : hf.toLp f ∈ space μ p := mem_of_rep μ p _ _ FactorCode.scalar_measurable hf.coeFn_toLp
  obtain ⟨g, hg, he⟩ := exists_rep μ q _ (hle hmem)
  refine ⟨FactorCode.scalar_embedding.invFun ∘ g,
    FactorCode.scalar_embedding.measurable_invFun.comp hg, ?_⟩
  filter_upwards [hf.coeFn_toLp, he] with x hx hex
  have hh : f x = g (q x) := hx.symm.trans hex
  change p x = FactorCode.scalar_embedding.invFun (g (q x))
  rw [← hh]
  exact (FactorCode.scalar_embedding.leftInverse_invFun (p x)).symm

end EuclideanFiveColor.FactorLp
namespace EuclideanFiveColor.CountableApprox
open MeasureTheory
variable {Y : Type*} [MeasurableSpace Y]

def truncate (n : ℕ) (y : ℕ → Y) : Fin n → Y := fun i => y i

lemma truncate_measurable (n : ℕ) : Measurable (truncate (Y := Y) n) :=
  Measurable.of_eval fun i => measurable_pi_apply (i : ℕ)

lemma truncate_mono : Monotone (fun n => (inferInstance : MeasurableSpace (Fin n → Y)).comap (truncate n)) := by
  intro n m hnm
  rw [← measurable_iff_comap_le]
  have hm : Measurable[(inferInstance : MeasurableSpace (Fin m → Y)).comap (truncate m)]
      (truncate (Y := Y) m) := Measurable.of_comap_le le_rfl
  refine @Measurable.of_eval (ℕ → Y) (Fin n) (fun _ => Y)
    (MeasurableSpace.comap (truncate m) inferInstance) (fun _ => inferInstance) (truncate n) ?_
  intro i
  exact (measurable_pi_apply (⟨i, lt_of_lt_of_le i.isLt hnm⟩ : Fin m)).comp hm

lemma truncate_generate : (⨆ n, (inferInstance : MeasurableSpace (Fin n → Y)).comap (truncate n)) =
    (inferInstance : MeasurableSpace (ℕ → Y)) := by
  apply le_antisymm (iSup_le fun n => (truncate_measurable n).comap_le)
  have hm (n : ℕ) : Measurable[⨆ n, (inferInstance : MeasurableSpace (Fin n → Y)).comap (truncate n)]
      (truncate (Y := Y) n) := Measurable.of_comap_le (le_iSup (fun n => MeasurableSpace.comap (truncate (Y := Y) n) (inferInstance : MeasurableSpace (Fin n → Y))) n)
  have hi : Measurable[⨆ n, (inferInstance : MeasurableSpace (Fin n → Y)).comap (truncate n)]
      (id : (ℕ → Y) → (ℕ → Y)) := by
    refine @Measurable.of_eval (ℕ → Y) ℕ (fun _ => Y)
      (⨆ n, MeasurableSpace.comap (truncate n) (inferInstance : MeasurableSpace (Fin n → Y)))
      (fun _ => inferInstance) id ?_
    intro n
    exact (measurable_pi_apply (⟨n, Nat.lt_succ_self n⟩ : Fin (n+1))).comp (hm (n+1))
  simpa using hi.comap_le

lemma bounded_approximation (ν : Measure (ℕ → Y)) [IsProbabilityMeasure ν]
    (m : ℕ) (H : (ℕ → Y) → Fin m → ℂ) (hH : Measurable H)
    (C : ℝ) (hC : 0 ≤ C) (hB : ∀ y, ‖H y‖ ≤ C) (ε : ℝ) (hε : 0 < ε) :
    ∃ n, ∃ H₀ : (Fin n → Y) → Fin m → ℂ, Measurable H₀ ∧ (∀ y, ‖H₀ y‖ ≤ 2*C) ∧
      Integrable (fun y => dist (H y) (H₀ (truncate n y))^2) ν ∧
      (∫ y, dist (H y) (H₀ (truncate n y))^2 ∂ν) < ε^2 :=
  LimitDensity.generated_factor_approximation ν truncate truncate_measurable truncate_mono truncate_generate
    m H hH C hC hB ε hε

end EuclideanFiveColor.CountableApprox
namespace EuclideanFiveColor.ChainJoin
open MeasureTheory
variable {K X Y : Type*} [Group K] [Countable K]
  [MeasurableSpace X] [MeasurableSpace Y] [StandardBorelSpace Y] [Nonempty Y]
  [MulAction K X] [MulAction K Y] [MeasurableConstSMul K X] [MeasurableConstSMul K Y]

def joint (q : ℕ → X → Y) (x : X) : ℕ → Y := fun n => q n x

def code (q : ℕ → X → Y) : X → OrbitSpace K := FactorCode.encode (joint q)

omit [StandardBorelSpace Y] [Nonempty Y] in
lemma joint_measurable (q : ℕ → X → Y) (hq : ∀ n, Measurable (q n)) : Measurable (joint q) :=
  Measurable.of_eval hq

omit [Nonempty Y] [MulAction K Y] [MeasurableConstSMul K Y] in
lemma code_measurable (q : ℕ → X → Y) (hq : ∀ n, Measurable (q n)) : Measurable (code (K := K) q) :=
  FactorCode.encode_measurable (joint_measurable q hq)

omit [Countable K] [MeasurableSpace X] [Nonempty Y] [MulAction K Y] [MeasurableConstSMul K X] [MeasurableConstSMul K Y] in
lemma code_equivariant (q : ℕ → X → Y) (k : K) (x : X) :
    code (K := K) q (k • x) = k • code q x := FactorCode.encode_equivariant _ _ _

omit [MulAction K Y] [MeasurableConstSMul K X] [MeasurableConstSMul K Y] in
lemma le_code (μ : Measure X) (q : ℕ → X → Y) (n : ℕ) :
    FactorLp.space μ (q n) ≤ FactorLp.space μ (code (K := K) q) := by
  apply FactorLp.le_of_factor μ (q n) (code q)
    (fun z => (FactorCode.decode (K := K) (Y := ℕ → Y) z) n)
    ((measurable_pi_apply n).comp FactorCode.decode_measurable)
  exact Filter.Eventually.of_forall fun x => by
    dsimp only [Function.comp_apply, code]
    rw [FactorCode.decode_encode]
    rfl

omit [Countable K] [MeasurableSpace Y] [MeasurableConstSMul K X] [MeasurableConstSMul K Y] [Nonempty Y] [StandardBorelSpace Y] in
lemma joint_equivariant (μ : Measure X) (q : ℕ → X → Y)
    (hqe : ∀ n (k : K), ∀ᵐ x ∂μ, q n (k • x) = k • q n x) (k : K) :
    ∀ᵐ x ∂μ, joint q (k • x) = k • joint q x := by
  filter_upwards [ae_all_iff.mpr (fun n => hqe n k)] with x hx
  exact funext hx

omit [StandardBorelSpace Y] [Nonempty Y] in
lemma finite_upper (μ : Measure X) (q : ℕ → X → Y)
    (hc : ∀ i j, FactorLp.space μ (q i) ≤ FactorLp.space μ (q j) ∨
      FactorLp.space μ (q j) ≤ FactorLp.space μ (q i)) (n : ℕ) :
    ∃ j, ∀ i < n, FactorLp.space μ (q i) ≤ FactorLp.space μ (q j) := by
  induction n with
  | zero => exact ⟨0, by simp⟩
  | succ n ih =>
    obtain ⟨j, hj⟩ := ih
    obtain hij | hji := hc j n
    · refine ⟨n, fun i hi => ?_⟩
      obtain hi | rfl := Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi)
      · exact (hj i hi).trans hij
      · exact le_rfl
    · refine ⟨j, fun i hi => ?_⟩
      obtain hi | rfl := Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi)
      · exact hj i hi
      · exact hji

omit [MeasurableConstSMul K X] in
lemma approximation (μ : Measure X) [IsProbabilityMeasure μ]
    (q : ℕ → X → Y) (hq : ∀ n, Measurable (q n))
    (hqe : ∀ n (k : K), ∀ᵐ x ∂μ, q n (k • x) = k • q n x)
    (hc : ∀ i j, FactorLp.space μ (q i) ≤ FactorLp.space μ (q j) ∨
      FactorLp.space μ (q j) ≤ FactorLp.space μ (q i))
    (m : ℕ) (H : OrbitSpace K → Fin m → ℂ) (hH : Measurable H)
    (hB : ∃ C : ℝ, ∀ z, ‖H z‖ ≤ C) (ε : ℝ) (hε : 0 < ε) :
    ∃ j, ∃ H₀ : Y → Fin m → ℂ, Measurable H₀ ∧ (∃ C : ℝ, ∀ y, ‖H₀ y‖ ≤ C) ∧
      Integrable (fun x => dist (H (code q x)) (H₀ (q j x))^2) μ ∧
      (∫ x, dist (H (code q x)) (H₀ (q j x))^2 ∂μ) < ε^2 := by
  classical
  obtain ⟨C, hC⟩ := hB
  let C' := max C 0
  have hC' : 0 ≤ C' := le_max_right _ _
  let J := joint q
  have hJ := joint_measurable q hq
  let E : (ℕ → Y) → OrbitSpace K := FactorCode.encode id
  have hE : Measurable E := FactorCode.encode_measurable measurable_id
  obtain ⟨n, Hn, hHn, hHnB, hi, he⟩ := CountableApprox.bounded_approximation (μ.map J)
    m (H ∘ E) (hH.comp hE) C' hC' (fun y => (hC _).trans (le_max_left _ _)) ε hε
  obtain ⟨j, hj⟩ := finite_upper μ q hc n
  have hfac (i : Fin n) : ∃ r : Y → Y, Measurable r ∧ q i =ᵐ[μ] r ∘ q j :=
    FactorLp.factor_of_le μ (q i) (q j) (hq i) (hj i i.isLt)
  choose r hr hre using hfac
  let R : Y → Fin n → Y := fun y i => r i y
  have hR : Measurable R := Measurable.of_eval hr
  have hEq := FactorCode.encode_as_comp (K := K) μ J (joint_equivariant μ q hqe)
  have hEq' : (fun x => dist ((H ∘ E) (J x)) (Hn (CountableApprox.truncate n (J x)))^2) =ᵐ[μ]
      (fun x => dist (H (code q x)) ((Hn ∘ R) (q j x))^2) := by
    filter_upwards [hEq, ae_all_iff.mpr hre] with x hx hxr
    have hp : CountableApprox.truncate n (J x) = R (q j x) := funext hxr
    change dist (H (E (J x))) _ ^ 2 = _
    change code (K := K) q x = E (J x) at hx
    rw [← hx, hp]
    rfl
  refine ⟨j, Hn ∘ R, hHn.comp hR, ⟨2*C', fun y => hHnB _⟩, ?_, ?_⟩
  · exact (hi.comp_measurable hJ).congr hEq'
  · rw [← integral_congr_ae hEq', ← integral_map hJ.aemeasurable hi.aestronglyMeasurable]
    exact he

end EuclideanFiveColor.ChainJoin
namespace EuclideanFiveColor.SeparableZorn
open TopologicalSpace
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [SecondCountableTopology E]

lemma countable_cover (S : Set (Submodule ℂ E)) (hS : S.Nonempty) :
    ∃ p : ℕ → S, ∀ V : Submodule ℂ E, IsClosed (V : Set E) →
      (∀ n, (p n).val ≤ V) → ∀ U ∈ S, U ≤ V := by
  classical
  let D : Set E := {x | ∃ U ∈ S, x ∈ U}
  have : Nonempty D := by
    obtain ⟨U, hU⟩ := hS
    exact ⟨⟨0, U, hU, U.zero_mem⟩⟩
  obtain ⟨u, hu⟩ := exists_dense_seq D
  have hU (n : ℕ) : ∃ U : S, (u n).val ∈ U.val := by
    obtain ⟨U, hU, hx⟩ := (u n).property
    exact ⟨⟨U, hU⟩, hx⟩
  choose p hp using hU
  refine ⟨p, ?_⟩
  intro V hc hV U hUS x hx
  have hcl : IsClosed ((Subtype.val : D → E) ⁻¹' (V : Set E)) := hc.preimage continuous_subtype_val
  have hsub : Set.range u ⊆ (Subtype.val : D → E) ⁻¹' (V : Set E) := by
    rintro _ ⟨n, rfl⟩
    exact hV n (hp n)
  have hwhole := closure_minimal hsub hcl
  rw [hu.closure_range] at hwhole
  exact hwhole (Set.mem_univ (⟨x, U, hUS, hx⟩ : D))

lemma exists_maximal {A : Type*} [Preorder A] [Nonempty A]
    (F : A → Submodule ℂ E) (hF : ∀ a, IsClosed (F a : Set E))
    (hord : ∀ a b, a ≤ b ↔ F a ≤ F b)
    (hseq : ∀ p : ℕ → A, (∀ i j, p i ≤ p j ∨ p j ≤ p i) →
      ∃ a, ∀ i, p i ≤ a) : ∃ a : A, IsMax a := by
  classical
  apply zorn_le_nonempty
  intro c hc hne
  obtain ⟨p, hp⟩ := countable_cover (F '' c) (hne.image F)
  have hrep (n : ℕ) : ∃ a : c, F a = (p n).val := by
    obtain ⟨a, ha, he⟩ := (p n).property
    exact ⟨⟨a, ha⟩, he⟩
  choose a ha using hrep
  have haorder (i j : ℕ) : (a i).val ≤ (a j).val ∨ (a j).val ≤ (a i).val :=
    hc.total (a i).property (a j).property
  obtain ⟨b, hb⟩ := hseq (fun n => (a n).val) haorder
  refine ⟨b, ?_⟩
  intro d hd
  apply (hord d b).mpr
  exact hp (F b) (hF b) (fun n => by rw [← ha n]; exact (hord _ _).mp (hb n))
    (F d) ⟨d, hd, rfl⟩

end EuclideanFiveColor.SeparableZorn
namespace EuclideanFiveColor.CodedMax
open MeasureTheory
variable {K X : Type*} [Group K] [Countable K] [MeasurableSpace X]
  [MulAction K X] [MeasurableConstSMul K X]

structure Model (μ : Measure X) (Good : (X → OrbitSpace K) → Prop) where
  map : X → OrbitSpace K
  measurable : Measurable map
  equivariant : ∀ k : K, ∀ᵐ x ∂μ, map (k • x) = k • map x
  good : Good map

instance (μ : Measure X) (Good : (X → OrbitSpace K) → Prop) : Preorder (Model μ Good) where
  le a b := FactorLp.space μ a.map ≤ FactorLp.space μ b.map
  le_refl _ := le_rfl
  le_trans _ _ _ := le_trans

lemma exists_maximal (μ : Measure X) [IsProbabilityMeasure μ] [StandardBorelSpace X]
    (Good : (X → OrbitSpace K) → Prop) (hbase : Nonempty (Model μ Good))
    (hjoin : ∀ q : ℕ → X → OrbitSpace K, (∀ n, Measurable (q n)) →
      (∀ n (k : K), ∀ᵐ x ∂μ, q n (k • x) = k • q n x) → (∀ n, Good (q n)) →
      (∀ i j, FactorLp.space μ (q i) ≤ FactorLp.space μ (q j) ∨
        FactorLp.space μ (q j) ≤ FactorLp.space μ (q i)) → Good (ChainJoin.code q)) :
    ∃ a : Model μ Good, IsMax a := by
  have := hbase
  have : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  apply SeparableZorn.exists_maximal (fun a : Model μ Good => FactorLp.space μ a.map)
    (fun a => FactorLp.isClosed μ a.measurable) (fun _ _ => Iff.rfl)
  intro p hc
  let q := fun n => (p n).map
  have hq (n : ℕ) := (p n).measurable
  have hqe (n : ℕ) := (p n).equivariant
  have hcg : Good (ChainJoin.code q) := hjoin q hq hqe (fun n => (p n).good) hc
  let a : Model μ Good := ⟨ChainJoin.code q, ChainJoin.code_measurable q hq,
    fun k => Filter.Eventually.of_forall (ChainJoin.code_equivariant q k), hcg⟩
  exact ⟨a, fun n => ChainJoin.le_code μ q n⟩

end EuclideanFiveColor.CodedMax

end

end OAI
