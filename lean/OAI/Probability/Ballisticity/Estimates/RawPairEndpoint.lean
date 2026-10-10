import Mathlib
import OAI.Probability.Ballisticity.Walk.ClippedPairGrowth

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

noncomputable def prefixEndpoint {d : ℕ} (ℓ : Vector d) (x : Lattice d)
    (H : ℕ) (X : Path d) : Lattice d :=
  x + recordIndexPosition ℓ H (fun j => X j-x)

lemma measurable_prefixEndpoint {d : ℕ} (ℓ : Vector d) (x : Lattice d) (H : ℕ) :
    Measurable (prefixEndpoint ℓ x H) := by
  exact measurable_const.add ((measurable_recordIndexPosition ℓ H).comp
    (Measurable.of_eval fun j => (measurable_of_countable (fun u : Lattice d => u-x)).comp (measurable_pi_apply j)))

def PairEndpointEvent {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (x y : Lattice d) (H : ℕ) (z : ℝ) : Set (Path d × Path d) :=
  {p | p.1 ∈ Hit (Strip ℓ x H) (Upper ℓ x H) ∧
    p.2 ∈ Hit (Strip ℓ y H) (Upper ℓ y H) ∧
    z ≤ signedCoordinate f (prefixEndpoint ℓ y H p.2-prefixEndpoint ℓ x H p.1)}

lemma measurableSet_pairEndpointEvent {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (x y : Lattice d) (H : ℕ) (z : ℝ) :
    MeasurableSet (PairEndpointEvent ℓ f x y H z) := by
  apply (measurableSet_hit _ _ |>.preimage measurable_fst).inter
  apply (measurableSet_hit _ _ |>.preimage measurable_snd).inter
  exact measurableSet_le measurable_const ((measurable_of_countable (signedCoordinate f)).comp
    (((measurable_prefixEndpoint ℓ y H).comp measurable_snd).sub
      ((measurable_prefixEndpoint ℓ x H).comp measurable_fst)))

noncomputable def rawPairEndpointMass {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (H : ℕ) (z : ℝ) (π : Measure (Lattice d × Lattice d)) (ω : Environment d) : ℝ :=
  ∫ x, ((quenchedKernel (ω,x.1)).prod (quenchedKernel (ω,x.2))).real
    (PairEndpointEvent ℓ f x.1 x.2 H z) ∂π

lemma signedCoordinate_sub_add {d : ℕ} (f : Direction d) (x y u v : Lattice d) :
    signedCoordinate f ((y+v)-(x+u)) =
      signedCoordinate f (y-x)+signedCoordinate f v-signedCoordinate f u := by
  simp only [signedCoordinate,Pi.sub_apply,Pi.add_apply,Int.cast_sub,Int.cast_add]
  split_ifs <;> ring

lemma tubePrefix_endpoint_bound {d : ℕ} (e f : Direction d) (x : Lattice d)
    (θ z : ℝ) {H : ℕ} (hH : 0 < H) (X : Path d)
    (h0 : X 0=x) (hnn : ∀ n, ∃ g, X (n+1)=X n+step g)
    (hX : X ∈ TubePrefix (realPosition (step e)) f x θ z H) :
    X ∈ Hit (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H) ∧
    |signedCoordinate f (recordIndexPosition (realPosition (step e)) H (fun j => X j-x))-(H:ℝ)*θ| ≤ z := by
  rw [tubePrefix_eq_curvePrefix] at hX
  have hh := (curvePrefix_iff e f x _ z hH X h0 hnn).mp hX
  exact ⟨hh.1,hh.2 H le_rfl⟩

lemma endpointPrefix_endpoint_ae {d : ℕ} (e : Direction d) (x : Lattice d)
    {H : ℕ} (hH : 0 < H) (ω : Environment d) (A : Set (Lattice d)) :
    ∀ᵐ X ∂quenchedKernel (ω,x), X ∈ EndpointPrefix (realPosition (step e)) x H A →
      X ∈ Hit (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H) ∧
      prefixEndpoint (realPosition (step e)) x H X ∈ A := by
  filter_upwards [quenched_initial_ae (ω,x),quenched_nearest_neighbor (ω,x)] with X h0 hnn hX
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hX
  have hh : X ∈ HitAt (Strip (realPosition (step e)) x H) (Upper (realPosition (step e)) x H) n :=
    ⟨hn.1.1,hn.2⟩
  refine ⟨Set.mem_iUnion.mpr ⟨n,hh⟩,?_⟩
  dsimp [prefixEndpoint]
  rw [coordinate_hitAt_record e x X h0 hnn hH hh]
  simpa only [add_sub_cancel] using hn.1.2

lemma quenched_pair_regular {d : ℕ} (ω : Environment d) (x y : Lattice d) :
    ∀ᵐ p ∂(quenchedKernel (ω,x)).prod (quenchedKernel (ω,y)),
      (p.1 0=x ∧ ∀ n, ∃ g, p.1 (n+1)=p.1 n+step g) ∧
      (p.2 0=y ∧ ∀ n, ∃ g, p.2 (n+1)=p.2 n+step g) := by
  exact (Measure.quasiMeasurePreserving_fst.ae (quenched_initial_ae (ω,x) |>.and (quenched_nearest_neighbor (ω,x)))).and
    (Measure.quasiMeasurePreserving_snd.ae (quenched_initial_ae (ω,y) |>.and (quenched_nearest_neighbor (ω,y))))

lemma central_pair_mass_le {d : ℕ} (e f : Direction d) (x y : Lattice d)
    (θ z b : ℝ) {H : ℕ} (hH : 0 < H) (ω : Environment d)
    (hgap : b+2*z ≤ signedCoordinate f (y-x)) :
    centralPrefixMass (realPosition (step e)) f θ z H ω x*
      centralPrefixMass (realPosition (step e)) f θ z H ω y ≤
    ((quenchedKernel (ω,x)).prod (quenchedKernel (ω,y))).real
      (PairEndpointEvent (realPosition (step e)) f x y H b) := by
  have hs : (TubePrefix (realPosition (step e)) f x θ z H ×ˢ
      TubePrefix (realPosition (step e)) f y θ z H) ≤ᵐ[
      (quenchedKernel (ω,x)).prod (quenchedKernel (ω,y))]
      PairEndpointEvent (realPosition (step e)) f x y H b := by
    filter_upwards [quenched_pair_regular ω x y] with p hp hmem
    have hx := tubePrefix_endpoint_bound e f x θ z hH p.1 hp.1.1 hp.1.2 hmem.1
    have hy := tubePrefix_endpoint_bound e f y θ z hH p.2 hp.2.1 hp.2.2 hmem.2
    refine ⟨hx.1,hy.1,?_⟩
    rw [prefixEndpoint,prefixEndpoint,signedCoordinate_sub_add]
    have hx' := (abs_le.mp hx.2).2
    have hy' := (abs_le.mp hy.2).1
    linarith
  have hh := measure_mono_ae hs
  have hr := ENNReal.toReal_mono (measure_ne_top _ _) hh
  simpa only [Measure.prod_prod,ENNReal.toReal_mul,centralPrefixMass,Measure.real] using hr
lemma jump_central_pair_mass_le {d : ℕ} (e f : Direction d) (x y : Lattice d)
    (θ z a s b : ℝ) (hs : s=1 ∨ s= -1) {H : ℕ} (hH : 0 < H) (ω : Environment d)
    (hgap : b+z-a ≤ signedCoordinate f (y-x)) :
    jumpPrefixMass (realPosition (step e)) f ((H:ℝ)*θ) a s H ω (if s=1 then y else x)*
      centralPrefixMass (realPosition (step e)) f θ z H ω (if s=1 then x else y) ≤
    ((quenchedKernel (ω,x)).prod (quenchedKernel (ω,y))).real
      (PairEndpointEvent (realPosition (step e)) f x y H b) := by
  let ℓ := realPosition (step e)
  let A := fun w => EndpointPrefix ℓ w H {v | a < s*(signedCoordinate f (v-w)-(H:ℝ)*θ)}
  have hx := endpointPrefix_endpoint_ae e x hH ω {v | a < s*(signedCoordinate f (v-x)-(H:ℝ)*θ)}
  have hy := endpointPrefix_endpoint_ae e y hH ω {v | a < s*(signedCoordinate f (v-y)-(H:ℝ)*θ)}
  have hAE := (Measure.quasiMeasurePreserving_fst.ae hx).and (Measure.quasiMeasurePreserving_snd.ae hy)
  rcases hs with rfl | rfl
  · have hs : (TubePrefix ℓ f x θ z H ×ˢ A y) ≤ᵐ[
        (quenchedKernel (ω,x)).prod (quenchedKernel (ω,y))]
        PairEndpointEvent ℓ f x y H b := by
      filter_upwards [quenched_pair_regular ω x y,hAE] with p hp he hmem
      have hc := tubePrefix_endpoint_bound e f x θ z hH p.1 hp.1.1 hp.1.2 hmem.1
      have hj := he.2 hmem.2
      refine ⟨hc.1,hj.1,?_⟩
      have hb := (abs_le.mp hc.2).2
      have hj' := hj.2
      simp only [prefixEndpoint,add_sub_cancel_left,one_mul] at hj'
      rw [prefixEndpoint,prefixEndpoint,signedCoordinate_sub_add]
      linarith
    have hh := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hs)
    simpa only [Measure.prod_prod,ENNReal.toReal_mul,centralPrefixMass,jumpPrefixMass,A,
      Measure.real,ite_true,mul_comm] using hh
  · have hs : (A x ×ˢ TubePrefix ℓ f y θ z H) ≤ᵐ[
        (quenchedKernel (ω,x)).prod (quenchedKernel (ω,y))]
        PairEndpointEvent ℓ f x y H b := by
      filter_upwards [quenched_pair_regular ω x y,hAE] with p hp he hmem
      have hj := he.1 hmem.1
      have hc := tubePrefix_endpoint_bound e f y θ z hH p.2 hp.2.1 hp.2.2 hmem.2
      refine ⟨hj.1,hc.1,?_⟩
      have hb := (abs_le.mp hc.2).1
      have hj' := hj.2
      simp only [prefixEndpoint,add_sub_cancel_left,neg_one_mul] at hj'
      rw [prefixEndpoint,prefixEndpoint,signedCoordinate_sub_add]
      linarith
    have hh := ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hs)
    simpa only [Measure.prod_prod,ENNReal.toReal_mul,centralPrefixMass,jumpPrefixMass,A,
      Measure.real,show (-1:ℝ) ≠ 1 by norm_num,ite_false] using hh
end DirectionalTransience

end

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience
lemma integral_lower_from_fraction {I : Type*} [MeasurableSpace I]
    (π : Measure I) [IsProbabilityMeasure π] (A : I → Prop)
    (hA : MeasurableSet {x | A x}) (G : I → ℝ) (hG : Measurable G)
    (hG0 : ∀ x, 0 ≤ G x) (hG1 : ∀ x, G x ≤ 1)
    {c g : ℝ} (hg : 0 ≤ g) (hgood : ∀ x, A x → g ≤ G x)
    (hfrac : c ≤ ∫ x, if A x then (1:ℝ) else 0 ∂π) :
    c*g ≤ ∫ x, G x ∂π := by
  have hI : Integrable G π := (integrable_const (1:ℝ)).mono' hG.aestronglyMeasurable
    (ae_of_all _ fun x => by rw [Real.norm_eq_abs,abs_of_nonneg (hG0 x)]; exact hG1 x)
  have hII : Integrable (fun x => if A x then (1:ℝ) else 0) π := by
    have he : (fun x => if A x then (1:ℝ) else 0) = ({x | A x}).indicator (fun _ => (1:ℝ)) := by
      funext x; simp [Set.indicator]
    rw [he]
    exact (integrable_const _).indicator hA
  have hh := integral_mono (hII.mul_const g) hI (fun x => ?_)
  · rw [integral_mul_const] at hh
    exact (mul_le_mul_of_nonneg_right hfrac hg).trans hh
  · split_ifs with hx
    · simpa using hgood x hx
    · simpa using hG0 x

noncomputable def pairCentralRetainedMass {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (θ z : ℝ) (H : ℕ) (π : Measure (Lattice d × Lattice d)) (ω : Environment d) : ℝ :=
  ∫ x, centralPrefixMass ℓ f θ z H ω x.1*centralPrefixMass ℓ f θ z H ω x.2 ∂π
noncomputable def pairJumpRetainedMass {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (θ z a s : ℝ) (H : ℕ) (π : Measure (Lattice d × Lattice d)) (ω : Environment d) : ℝ :=
  ∫ x, jumpPrefixMass ℓ f ((H:ℝ)*θ) a s H ω (if s=1 then x.2 else x.1)*
    centralPrefixMass ℓ f θ z H ω (if s=1 then x.1 else x.2) ∂π

lemma centralPrefixMass_bounds {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (θ z : ℝ) (H : ℕ) (ω : Environment d) (x : Lattice d) :
    0 ≤ centralPrefixMass ℓ f θ z H ω x ∧ centralPrefixMass ℓ f θ z H ω x ≤ 1 :=
  ⟨measureReal_nonneg,measureReal_le_one⟩
lemma jumpPrefixMass_bounds {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (b a s : ℝ) (H : ℕ) (ω : Environment d) (x : Lattice d) :
    0 ≤ jumpPrefixMass ℓ f b a s H ω x ∧ jumpPrefixMass ℓ f b a s H ω x ≤ 1 :=
  ⟨measureReal_nonneg,measureReal_le_one⟩
lemma pair_retained_mass_of_favorable_fraction {d : ℕ} (ℓ : Vector d) (f : Direction d)
    (θ z a s : ℝ) (H : ℕ) (π : Measure (Lattice d × Lattice d)) [IsProbabilityMeasure π]
    (ω : Environment d) {c j d₀ : ℝ} (hj : 0 ≤ j) (hd : 0 ≤ d₀)
    (hfrac : c ≤ ∫ x,
      if j ≤ jumpPrefixMass ℓ f ((H:ℝ)*θ) a s H ω (if s=1 then x.2 else x.1) ∧
        d₀ ≤ centralPrefixMass ℓ f θ z H ω x.1 ∧
        d₀ ≤ centralPrefixMass ℓ f θ z H ω x.2
      then (1:ℝ) else 0 ∂π) :
    c*d₀^2 ≤ pairCentralRetainedMass ℓ f θ z H π ω ∧
    c*(j*d₀) ≤ pairJumpRetainedMass ℓ f θ z a s H π ω := by
  let J := jumpPrefixMass ℓ f ((H:ℝ)*θ) a s H ω
  let C := centralPrefixMass ℓ f θ z H ω
  let A := fun x : Lattice d × Lattice d => j ≤ J (if s=1 then x.2 else x.1) ∧ d₀ ≤ C x.1 ∧ d₀ ≤ C x.2
  have hf : c ≤ ∫ x, @ite ℝ (A x) (Classical.propDecidable _) 1 0 ∂π := by
    convert hfrac using 1
    apply integral_congr_ae
    filter_upwards [] with x
    dsimp [A,J,C]
    split_ifs <;> rfl
  have hJ (x) := jumpPrefixMass_bounds ℓ f ((H:ℝ)*θ) a s H ω x
  have hC (x) := centralPrefixMass_bounds ℓ f θ z H ω x
  constructor
  · apply integral_lower_from_fraction π A (Set.to_countable _ |>.measurableSet)
      (fun x => C x.1*C x.2) (measurable_of_countable _)
      (fun x => mul_nonneg (hC x.1).1 (hC x.2).1)
      (fun x => (mul_le_of_le_one_left (hC x.2).1 (hC x.1).2).trans (hC x.2).2)
      (sq_nonneg d₀) (fun x hx => ?_) hf
    simpa only [pow_two] using mul_le_mul hx.2.1 hx.2.2 hd (hd.trans hx.2.1)
  · apply integral_lower_from_fraction π A (Set.to_countable _ |>.measurableSet)
      (fun x => J (if s=1 then x.2 else x.1)*C (if s=1 then x.1 else x.2)) (measurable_of_countable _)
      (fun x => mul_nonneg (hJ _).1 (hC _).1)
      (fun x => (mul_le_of_le_one_left (hC (if s=1 then x.1 else x.2)).1
        (hJ (if s=1 then x.2 else x.1)).2).trans (hC (if s=1 then x.1 else x.2)).2)
      (mul_nonneg hj hd) (fun x hx => ?_) hf
    apply mul_le_mul hx.1 _ hd (hj.trans hx.1)
    split_ifs
    · exact hx.2.1
    · exact hx.2.2
end DirectionalTransience

end

end

end OAI
