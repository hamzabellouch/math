import OAI.Dynamics.ThreeTorus.DynamicsLimit

namespace OAI

/-! Physical Hilbert space, L2 limiting real orbit, full test density, and complete physical basis. -/

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology ComplexConjugate
namespace ThreeTorus

abbrev PhysicalL2 := StageState.L2

def physicalIntegral : PhysicalL2 →L[ℂ] ℂ := innerSL ℂ (Lp.const 2 tripleVolume (1:ℂ))
lemma physicalIntegral_apply (f : PhysicalL2) : physicalIntegral f=∫ x, f x ∂tripleVolume := by
  change inner ℂ (Lp.const 2 tripleVolume (1:ℂ)) f = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_const 2 tripleVolume (1:ℂ)] with x hx
  simp only [hx,Function.const_apply,RCLike.inner_apply,map_one,mul_one]

def physicalMeanZero : Submodule ℂ PhysicalL2 := physicalIntegral.ker
lemma mem_physicalMeanZero (f : PhysicalL2) : f ∈ physicalMeanZero ↔ ∫ x, f x ∂tripleVolume=0 := by
  change physicalIntegral f=0 ↔ _
  rw [physicalIntegral_apply]
lemma physicalMeanZero_closed : IsClosed (physicalMeanZero : Set PhysicalL2) := physicalIntegral.isClosed_ker

def physicalCenter (f : PhysicalL2) : PhysicalL2 :=
  f - physicalIntegral f • Lp.const 2 tripleVolume (1:ℂ)
lemma continuous_physicalCenter : Continuous physicalCenter :=
  continuous_id.sub (physicalIntegral.continuous.smul continuous_const)
lemma physicalCenter_ae (f : PhysicalL2) : physicalCenter f =ᵐ[tripleVolume]
    fun x => f x-physicalIntegral f := by
  filter_upwards [Lp.coeFn_sub f (physicalIntegral f • Lp.const 2 tripleVolume (1:ℂ)),
    Lp.coeFn_smul (physicalIntegral f) (Lp.const 2 tripleVolume (1:ℂ)),
    Lp.coeFn_const 2 tripleVolume (1:ℂ)] with x hx hy hz
  simpa only [physicalCenter,Pi.sub_apply,Pi.smul_apply,hy,hz,Function.const_apply,smul_eq_mul,mul_one] using hx
lemma physicalCenter_mem (f : PhysicalL2) : physicalCenter f ∈ physicalMeanZero := by
  rw [mem_physicalMeanZero,integral_congr_ae (physicalCenter_ae f),
    integral_sub ((Lp.memLp f).integrable (by norm_num)) (integrable_const _)]
  simp [physicalIntegral_apply]
lemma physicalCenter_eq_self {f : PhysicalL2} (hf : f ∈ physicalMeanZero) : physicalCenter f=f := by
  change physicalIntegral f=0 at hf
  simp only [physicalCenter,hf,zero_smul,sub_zero]

def continuousCenter (g : C(TripleTorus,ℂ)) : C(TripleTorus,ℂ) :=
  g - ContinuousMap.const _ (∫ x, g x ∂tripleVolume)
lemma continuousCenter_centered (g : C(TripleTorus,ℂ)) :
    ∫ x, continuousCenter g x ∂tripleVolume=0 := by
  change (∫ x, g x-(∫ y, g y ∂tripleVolume) ∂tripleVolume)=0
  rw [integral_sub ((continuous_triple_memLp g.continuous).integrable (by norm_num)) (integrable_const _)]
  simp
lemma toLp_continuousCenter (g : C(TripleTorus,ℂ)) :
    ContinuousMap.toLp 2 tripleVolume ℂ (continuousCenter g)=
      physicalCenter (ContinuousMap.toLp 2 tripleVolume ℂ g) := by
  apply Lp.ext
  have hg := ContinuousMap.coeFn_toLp tripleVolume (𝕜 := ℂ) (p := 2) g
  have hi : physicalIntegral (ContinuousMap.toLp 2 tripleVolume ℂ g)=∫ x, g x ∂tripleVolume := by
    rw [physicalIntegral_apply,integral_congr_ae hg]
  filter_upwards [ContinuousMap.coeFn_toLp tripleVolume (𝕜 := ℂ) (p := 2) (continuousCenter g),
    physicalCenter_ae (ContinuousMap.toLp 2 tripleVolume ℂ g),hg] with x hx hy hz
  rw [hx,hy]
  change g x - (∫ y, g y ∂tripleVolume)=_
  rw [hi,hz]

lemma physical_real_closed : IsClosed {f : PhysicalL2 | ∀ᵐ x ∂tripleVolume, (f x).im=0} := by
  let I : PhysicalL2 →L[ℝ] Lp ℝ 2 tripleVolume := Complex.imCLM.compLpL 2 tripleVolume
  have he : {f : PhysicalL2 | ∀ᵐ x ∂tripleVolume, (f x).im=0}={f | I f=0} := by
    ext f
    constructor
    · intro h
      apply Lp.ext
      filter_upwards [Complex.imCLM.coeFn_compLp f,h,Lp.coeFn_zero ℝ 2 tripleVolume] with x hx hy hz
      exact hx.trans (hy.trans hz.symm)
    · intro h
      filter_upwards [Complex.imCLM.coeFn_compLp f,Lp.coeFn_zero ℝ 2 tripleVolume] with x hx hz
      change I f x=(f x).im at hx
      rw [h,hz] at hx
      exact hx.symm
  rw [he]
  exact isClosed_eq I.continuous continuous_const

namespace PhysicalTest
instance : TopologicalSpace PhysicalTest := TopologicalSpace.induced PhysicalTest.fn ContinuousMap.compactOpen
instance : SecondCountableTopology PhysicalTest :=
  (Topology.IsInducing.induced PhysicalTest.fn).secondCountableTopology
instance : Nonempty PhysicalTest := ⟨{
  fn := 0, real := by simp, centered := by simp, bound := by simp }⟩
lemma vec_eq_toLp (h : PhysicalTest) : h.vec=ContinuousMap.toLp 2 tripleVolume ℂ h.fn := by
  apply Lp.ext
  exact h.vec_ae.trans (ContinuousMap.coeFn_toLp tripleVolume h.fn).symm
lemma continuous_vec : Continuous (fun h : PhysicalTest => h.vec) := by
  have hh : Continuous (fun h : PhysicalTest => ContinuousMap.toLp 2 tripleVolume ℂ h.fn) :=
    (ContinuousMap.toLp 2 tripleVolume ℂ).continuous.comp
      (continuous_induced_dom : Continuous PhysicalTest.fn)
  convert hh using 1
  exact funext vec_eq_toLp
lemma vec_centered (h : PhysicalTest) : h.vec ∈ physicalMeanZero := by
  rw [mem_physicalMeanZero,integral_congr_ae h.vec_ae,h.centered]
end PhysicalTest

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus
namespace SmoothDynamics
variable (D : SmoothDynamics)

def homeo (k : ℤ) : TripleTorus ≃ₜ TripleTorus where
  toFun := D.map k
  invFun := D.map (-k)
  left_inv := by intro x; rw [← D.add,neg_add_cancel,D.zero]
  right_inv := by intro x; rw [← D.add,add_neg_cancel,D.zero]
  continuous_toFun := (D.map k).continuous
  continuous_invFun := (D.map (-k)).continuous

def orbit (f : PhysicalL2) (k : ℤ) : PhysicalL2 :=
  Lp.compMeasurePreserving (D.map k) (D.mp k) f
lemma orbit_ae (f : PhysicalL2) (k : ℤ) : D.orbit f k =ᵐ[tripleVolume]
    fun x => f (D.map k x) := Lp.coeFn_compMeasurePreserving f (D.mp k)
lemma orbit_centered {f : PhysicalL2} (hf : f ∈ physicalMeanZero) (k : ℤ) :
    D.orbit f k ∈ physicalMeanZero := by
  rw [mem_physicalMeanZero,integral_congr_ae (D.orbit_ae f k),
    (D.mp k).integral_comp (D.homeo k).toMeasurableEquiv.measurableEmbedding]
  exact (mem_physicalMeanZero f).mp hf

def laurent (f : PhysicalL2) (c : ℤ →₀ ℂ) : PhysicalL2 := c.sum (fun k a => a • D.orbit f k)
lemma laurent_mem_span (f : PhysicalL2) (c : ℤ →₀ ℂ) :
    D.laurent f c ∈ Submodule.span ℂ (Set.range (D.orbit f)) := by
  classical
  exact Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k,rfl⟩))

lemma tendsto_orbit {s : ℕ → StageState} {f : PhysicalL2}
    (hf : Tendsto (fun n => (s n).vec) atTop (𝓝 f))
    (hT : ∀ k, Tendsto (fun n => (s n).mapCont k) atTop (𝓝 (D.map k))) (k : ℤ) :
    Tendsto (fun n => (s n).orbit k) atTop (𝓝 (D.orbit f k)) :=
  hf.compMeasurePreservingLp (hT k) (fun n => (s n).mapPow_mp k) (D.mp k) (by norm_num)
lemma tendsto_laurent {s : ℕ → StageState} {f : PhysicalL2}
    (hf : Tendsto (fun n => (s n).vec) atTop (𝓝 f))
    (hT : ∀ k, Tendsto (fun n => (s n).mapCont k) atTop (𝓝 (D.map k))) (c : ℤ →₀ ℂ) :
    Tendsto (fun n => (s n).laurent c) atTop (𝓝 (D.laurent f c)) := by
  classical
  exact tendsto_finsetSum _ (fun k _ => (D.tendsto_orbit hf hT k).const_smul (c k))
end SmoothDynamics

/-- The diagonal produces an actual real centered vector and exact bilateral
orthonormality, while retaining EVERY earlier polynomial in the same limit map. -/
theorem exists_physical_limit (test : ℕ → PhysicalTest) (e : ℕ → ℝ)
    (he : ∀ n, 0 < e n) :
    ∃ D : SmoothDynamics, ∃ f : PhysicalL2,
      f ∈ physicalMeanZero ∧ (∀ᵐ x ∂tripleVolume, (f x).im=0) ∧
      Orthonormal ℂ (D.orbit f) ∧
      ∃ c : ℕ → (ℤ →₀ ℂ), ∀ i, dist (test i).vec (D.laurent f (c i)) ≤ e i := by
  let b (n : ℕ) : ℝ := (1/2)^n
  have hb (n : ℕ) : 0 < b n := pow_pos (by norm_num) _
  have hbs : Summable b := summable_geometric_of_lt_one (by norm_num) (by norm_num)
  obtain ⟨s,c,hv,hj,hc⟩ := exists_stage_diagonal test e b he hb
  have hC : CauchySeq (fun n => (s n).vec) :=
    cauchySeq_of_dist_le_of_summable b (fun n => (hv n).le) hbs
  obtain ⟨f,hf⟩ := cauchySeq_tendsto_of_complete hC
  obtain ⟨D,hT⟩ := smooth_dynamics_of_jets s hbs hj
  have hf0 : f ∈ physicalMeanZero := physicalMeanZero_closed.mem_of_tendsto hf
    (Eventually.of_forall (fun n => by
      change (s n).vec ∈ physicalMeanZero
      rw [mem_physicalMeanZero,integral_congr_ae (s n).vec_ae,(s n).vector_centered]))
  have hfr : ∀ᵐ x ∂tripleVolume, (f x).im=0 := physical_real_closed.mem_of_tendsto hf
    (Eventually.of_forall (fun n => by
      filter_upwards [(s n).vec_ae] with x hx
      rw [hx]
      exact Complex.conj_eq_iff_im.mp ((s n).vector_real x)))
  have ho : Orthonormal ℂ (D.orbit f) := by
    rw [orthonormal_iff_ite]
    intro k j
    have hL := (D.tendsto_orbit hf hT k).inner (𝕜 := ℂ) (D.tendsto_orbit hf hT j)
    have hE (n : ℕ) : inner ℂ ((s n).orbit k) ((s n).orbit j)=if k=j then 1 else 0 :=
      orthonormal_iff_ite.mp (s n).orbit_orthonormal k j
    simp only [hE] at hL
    exact tendsto_nhds_unique hL tendsto_const_nhds
  refine ⟨D,f,hf0,hfr,ho,c,fun i => ?_⟩
  exact le_of_tendsto (tendsto_const_nhds.dist (D.tendsto_laurent hf hT (c i)))
    (eventually_atTop.mpr ⟨i+1,fun n hn => (hc i n (by omega)).le⟩)

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology ComplexConjugate
namespace ThreeTorus

/-- Every real centered continuous vector belongs to the linear span of the
bounded physical tests, with its actual normalization scalar. -/
lemma continuous_real_mem_of_tests (K : Submodule ℂ PhysicalL2)
    (hK : ∀ h : PhysicalTest, h.vec ∈ K)
    (g : C(TripleTorus,ℂ)) (hg : ∀ x, conj (g x)=g x)
    (hgc : ∫ x, g x ∂tripleVolume=0) : ContinuousMap.toLp 2 tripleVolume ℂ g ∈ K := by
  let M : ℝ := ‖g‖+1
  have hM : 0 < M := by dsimp [M]; positivity
  have hMc : (M:ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  let h : PhysicalTest := {
    fn := (M:ℂ)⁻¹ • g,
    real := by
      intro x
      simp only [ContinuousMap.smul_apply,smul_eq_mul,map_mul,map_inv₀,Complex.conj_ofReal,hg],
    centered := by
      change (∫ x, (M:ℂ)⁻¹ • g x ∂tripleVolume)=0
      rw [integral_smul,hgc,smul_zero],
    bound := by
      intro x
      simp only [ContinuousMap.smul_apply,norm_smul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hM]
      have hx := g.norm_coe_le_norm x
      rw [inv_mul_eq_div]
      exact (div_le_one hM).mpr (hx.trans (by dsimp [M]; linarith)) }
  have hh : h.vec=(M:ℂ)⁻¹ • ContinuousMap.toLp 2 tripleVolume ℂ g := by
    rw [PhysicalTest.vec_eq_toLp]
    exact map_smul (ContinuousMap.toLp 2 tripleVolume ℂ) _ _
  have hm := K.smul_mem (M:ℂ) (hK h)
  rw [hh,smul_smul,mul_inv_cancel₀ hMc,one_smul] at hm
  exact hm

lemma continuous_centered_mem_of_tests (K : Submodule ℂ PhysicalL2)
    (hK : ∀ h : PhysicalTest, h.vec ∈ K)
    (g : C(TripleTorus,ℂ)) (hgc : ∫ x, g x ∂tripleVolume=0) :
    ContinuousMap.toLp 2 tripleVolume ℂ g ∈ K := by
  let r : C(TripleTorus,ℂ) := ⟨fun x => ((g x).re:ℂ),
    Complex.continuous_ofReal.comp (Complex.continuous_re.comp g.continuous)⟩
  let j : C(TripleTorus,ℂ) := ⟨fun x => ((g x).im:ℂ),
    Complex.continuous_ofReal.comp (Complex.continuous_im.comp g.continuous)⟩
  have hi : Integrable g tripleVolume := (continuous_triple_memLp g.continuous).integrable (by norm_num)
  have hr : ∫ x, r x ∂tripleVolume=0 := by
    change (∫ x, ((g x).re:ℂ) ∂tripleVolume)=0
    rw [integral_complex_ofReal]
    have hh := integral_re hi
    change (∫ x, (g x).re ∂tripleVolume)=(∫ x, g x ∂tripleVolume).re at hh
    rw [hh,hgc]
    simp
  have hj : ∫ x, j x ∂tripleVolume=0 := by
    change (∫ x, ((g x).im:ℂ) ∂tripleVolume)=0
    rw [integral_complex_ofReal]
    have hh := integral_im hi
    change (∫ x, (g x).im ∂tripleVolume)=(∫ x, g x ∂tripleVolume).im at hh
    rw [hh,hgc]
    simp
  have he : g=r+Complex.I • j := by
    ext x
    change g x=((g x).re:ℂ)+Complex.I*((g x).im:ℂ)
    simpa only [mul_comm] using (Complex.re_add_im (g x)).symm
  rw [he,map_add,map_smul]
  exact K.add_mem (continuous_real_mem_of_tests K hK r (by intro x; exact Complex.conj_ofReal _) hr)
    (K.smul_mem Complex.I (continuous_real_mem_of_tests K hK j (by intro x; exact Complex.conj_ofReal _) hj))

/-- Bounded real tests exhaust the FULL complex centered L2 space, not just a
real or cyclic subspace. -/
lemma physical_tests_total (K : Submodule ℂ PhysicalL2) (hclosed : IsClosed (K : Set PhysicalL2))
    (hK : ∀ h : PhysicalTest, h.vec ∈ K) {f : PhysicalL2} (hf : f ∈ physicalMeanZero) : f ∈ K := by
  have hd : DenseRange (ContinuousMap.toLp 2 tripleVolume ℂ : C(TripleTorus,ℂ) →L[ℂ] PhysicalL2) :=
    ContinuousMap.toLp_denseRange ℂ tripleVolume ℂ (p := 2) (by norm_num)
  have hh : physicalCenter f ∈ K := by
    apply hd.induction_on (p := fun x => physicalCenter x ∈ K) f (hclosed.preimage continuous_physicalCenter)
    intro g
    rw [← toLp_continuousCenter]
    exact continuous_centered_mem_of_tests K hK _ (continuousCenter_centered g)
  rwa [physicalCenter_eq_self hf] at hh

/-- A single honest countable family of real bounded centered continuous tests
suffices. Its full complex span is dense after closure. -/
theorem exists_total_physical_tests : ∃ test : ℕ → PhysicalTest,
    ∀ K : Submodule ℂ PhysicalL2, IsClosed (K : Set PhysicalL2) →
      (∀ n, (test n).vec ∈ K) → ∀ f ∈ physicalMeanZero, f ∈ K := by
  obtain ⟨test,htest⟩ := TopologicalSpace.exists_dense_seq PhysicalTest
  refine ⟨test,fun K hclosed hK f hf => physical_tests_total K hclosed ?_ hf⟩
  intro h
  exact htest.induction_on h (hclosed.preimage PhysicalTest.continuous_vec) hK

end ThreeTorus
end
end

section

noncomputable section
open Set Function Filter MeasureTheory
open scoped Topology BigOperators ComplexConjugate
namespace ThreeTorus

/-- Unconditional geometric spectral basis on the physical product torus.
The closure here is exactly the FULL complex kernel of the volume integral. -/
theorem exists_physical_basis : ∃ D : SmoothDynamics, ∃ f : PhysicalL2,
    f ∈ physicalMeanZero ∧ (∀ᵐ x ∂tripleVolume, (f x).im=0) ∧
    Orthonormal ℂ (D.orbit f) ∧
    (Submodule.span ℂ (Set.range (D.orbit f))).topologicalClosure=physicalMeanZero := by
  obtain ⟨test,htest⟩ := exists_total_physical_tests
  let a (n : ℕ) := test (Nat.unpair n).1
  let e (n : ℕ) : ℝ := (1/2)^((Nat.unpair n).2)
  have he (n : ℕ) : 0 < e n := pow_pos (by norm_num) _
  obtain ⟨D,f,hf,hfr,ho,c,hc⟩ := exists_physical_limit a e he
  let S := Submodule.span ℂ (Set.range (D.orbit f))
  have htestmem (i : ℕ) : (test i).vec ∈ S.topologicalClosure := by
    change (test i).vec ∈ closure (S : Set PhysicalL2)
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    have hz : Tendsto (fun m : ℕ => (1/2:ℝ)^m) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    obtain ⟨m,hm⟩ := (hz.eventually (gt_mem_nhds hε)).exists
    refine ⟨D.laurent f (c (Nat.pair i m)),D.laurent_mem_span f _,?_⟩
    have hh := hc (Nat.pair i m)
    simp only [a,e,Nat.unpair_pair] at hh
    exact hh.trans_lt hm
  refine ⟨D,f,hf,hfr,ho,le_antisymm ?_ ?_⟩
  · exact S.topologicalClosure_minimal
      (Submodule.span_le.mpr (by rintro _ ⟨k,rfl⟩; exact D.orbit_centered hf k))
      physicalMeanZero_closed
  · exact fun g hg => htest S.topologicalClosure S.isClosed_topologicalClosure htestmem g hg

end ThreeTorus
end
end

end OAI
