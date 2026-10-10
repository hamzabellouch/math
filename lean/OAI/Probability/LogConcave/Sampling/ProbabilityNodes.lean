import Mathlib
import OAI.Probability.LogConcave.Numerics.Correction
import OAI.Probability.LogConcave.Sampling.AngleNodes
import OAI.Probability.LogConcave.Sampling.MeanMaterialVector
import OAI.Probability.LogConcave.Numerics.LogMeshLength

namespace OAI

section
section
noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory Quadrature
open scoped Classical BigOperators NNReal

theorem mean_cell_taylor_rms (n : ℕ) :
    ∃C : ℝ,0≤C ∧ ∃k : ℕ,∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},
      ∀hF : Primitive F lam,∀(x : Point d) {r : ℝ},∀hr : 0<r,
      0<lam → ∀hl : (lam:ℝ)*r^2≤1/2,1≤d →
      ∀a b h : ℝ,0≤a → a≤b → b<1 → 0≤h → b-a≤h*(1-b) →
      ∀t∈Icc a b,
      Integrable (fun z => ‖meanPathJet hF x hr.le hl b 0 t z-
        chainTaylor (fun j v => meanPathJet hF x hr.le hl b j v z) n a t‖^2)
        (stdGaussian (Point d)) ∧
      (∫z,‖meanPathJet hF x hr.le hl b 0 t z-
        chainTaylor (fun j v => meanPathJet hF x hr.le hl b j v z) n a t‖^2
        ∂stdGaussian (Point d))≤
        (C*((lam:ℝ)*r)*Real.sqrt (d:ℝ)*(1+Real.log ((d:ℝ)+1))^k*h^(n+1))^2 := by
  obtain ⟨C,hC,k,hk⟩ := mean_path_taylor_rms n
  refine ⟨C,hC,k,?_⟩
  intro d F lam hF x r hr hlam hl hd a b h ha hab hb hh hcell t ht
  have hg := hk hF x hr hlam hl (ha.trans hab) hb hd a t ha ht.1 ht.2
  refine ⟨hg.1,hg.2.trans ?_⟩
  apply cell_taylor_budget ha ht.1 ht.2 hb hh hcell
  have hlog : 0≤Real.log ((d:ℝ)+1) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) d])
  positivity

lemma meanPathJet_taylor_continuous {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r b : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hb0 : 0≤b) (hb1 : b<1) (n : ℕ) (a t : ℝ) :
    Continuous (fun z => chainTaylor (fun j v => meanPathJet hF x hr hl b j v z) n a t) := by
  unfold chainTaylor
  apply continuous_finsetSum
  intro j _
  exact (meanPathJet_space_continuous hF x hr hl hb0 hb1 j a).const_smul
    ((j.factorial:ℝ)⁻¹*(t-a)^j)
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory ProbabilityTheory Quadrature
open scoped Classical BigOperators NNReal

def probabilityNodes (n : ℕ) (i : Fin (n+1)) : ℝ := (i:ℝ)/(n:ℝ)

lemma probabilityNodes_injective {n : ℕ} (hn : 0<n) : Function.Injective (probabilityNodes n) := by
  intro i j hij
  apply Fin.ext
  have hne : (n:ℝ)≠0 := by exact_mod_cast ne_of_gt hn
  have he : (i:ℝ)=(j:ℝ) := (div_left_inj' hne).mp hij
  exact_mod_cast he

lemma probabilityNodes_mem {n : ℕ} (hn : 0<n) (i : Fin (n+1)) : probabilityNodes n i∈Icc (0:ℝ) 1 := by
  have hp : (0:ℝ)<n := by exact_mod_cast hn
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) hp.le
  · apply (div_le_iff₀ hp).mpr
    simp only [one_mul]
    exact_mod_cast Nat.le_of_lt_succ i.2

theorem mean_cell_interpolation_rms (n : ℕ) (hn : 0<n) :
    ∃C : ℝ,0≤C ∧ ∃k : ℕ,∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},
      ∀hF : Primitive F lam,∀(x : Point d) {r : ℝ},∀hr : 0<r,
      0<lam → ∀hl : (lam:ℝ)*r^2≤1/2,1≤d →
      ∀a b h : ℝ,0≤a → a≤b → b<1 → 0≤h → b-a≤h*(1-b) →
      ∀t∈Icc (0:ℝ) 1,
      Integrable (fun z => ‖meanPathJet hF x hr.le hl b 0 (a+(b-a)*t) z-
        interpolation (probabilityNodes n)
          (fun i => meanPathJet hF x hr.le hl b 0 (a+(b-a)*probabilityNodes n i) z) t‖^2)
        (stdGaussian (Point d)) ∧
      (∫z,‖meanPathJet hF x hr.le hl b 0 (a+(b-a)*t) z-
        interpolation (probabilityNodes n)
          (fun i => meanPathJet hF x hr.le hl b 0 (a+(b-a)*probabilityNodes n i) z) t‖^2
        ∂stdGaussian (Point d))≤
        (C*((lam:ℝ)*r)*Real.sqrt (d:ℝ)*(1+Real.log ((d:ℝ)+1))^k*h^(n+1))^2 := by
  obtain ⟨C,hC,k,hk⟩ := mean_cell_taylor_rms n
  obtain ⟨A,hA,hA'⟩ := exists_basis_budget (probabilityNodes n)
  refine ⟨2*A*C,by positivity,k,?_⟩
  intro d F lam hF x r hr hlam hl hd a b h ha hab hb hh hcell t ht
  have hs {s : ℝ} (hs : s∈insert t (Set.range (probabilityNodes n))) : s∈Icc (0:ℝ) 1 := by
    rcases hs with he|⟨i,rfl⟩
    · simpa only [he] using ht
    · exact probabilityNodes_mem hn i
  have hscale {s : ℝ} (hs' : s∈Icc (0:ℝ) 1) : a+(b-a)*s∈Icc a b := by
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hab) hs'.1,
      mul_le_mul_of_nonneg_left hs'.2 (sub_nonneg.mpr hab)]
  have htay (s : ℝ) (hs' : s∈insert t (Set.range (probabilityNodes n))) :=
    hk hF x hr hlam hl hd a b h ha hab hb hh hcell _ (hscale (hs hs'))
  have hm (s : ℝ) (_ : s∈insert t (Set.range (probabilityNodes n))) :
      AEStronglyMeasurable (fun z => meanPathJet hF x hr.le hl b 0 (a+(b-a)*s) z-
        chainTaylor (fun j v => meanPathJet hF x hr.le hl b j v z) n a (a+(b-a)*s))
        (stdGaussian (Point d)) :=
    ((meanPathJet_space_continuous hF x hr.le hl (ha.trans hab) hb 0 _).sub
      (meanPathJet_taylor_continuous hF x hr.le hl (ha.trans hab) hb n a _)).aestronglyMeasurable
  have he := cell_chain_error_rms (probabilityNodes n) (probabilityNodes_injective hn) n
    (by simp) (meanPathJet hF x hr.le hl b) a (b-a) t (sq_nonneg _) hA (hA' t ht)
    hm (fun s hs => (htay s hs).1) (fun s hs => (htay s hs).2)
  refine ⟨he.1,he.2.trans_eq ?_⟩
  ring
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory
open scoped Classical BigOperators NNReal RealInnerProductSpace
open TensorEnergy Quadrature

local instance : DecidableEq Unit := Classical.decEq _

theorem harmonic_mean_interpolation_rms (n : ℕ) (hn : 0<n) :
    ∃C : ℝ,1≤C ∧ ∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},
      ∀_ : Primitive F lam,∀(x : Point d) {r R T : ℝ},
      0<r → 0<lam → (lam:ℝ)*r^2≤1/2 → 0<R → R^2≤1-T^2 → 0≤T → T<1 →
      ∀Ξ : Point (d+d) → ℝ → Point (d+d),
      (∀y v,v∈Icc (0:ℝ) 1 → HasDerivWithinAt (Ξ y)
        (skewLieField (centeringPotential F x r T) (harmonicSkew d) (Ξ y v)) (Icc (0:ℝ) 1) v) →
      Measurable (fun p : ℝ × Point (d+d) => Ξ p.2 p.1) →
      (∀v∈Icc (0:ℝ) 1,(gibbs (centeringPotential F x r T)).map (fun y => Ξ y v)=
        gibbs (centeringPotential F x r T)) →
      ∀z : ℝ,0≤z → z≤1 → ∀v∈Icc (0:ℝ) 1,
      let M := fun s y => tensorVector (centeringMeanArray F x r T) (Ξ y s)
      Integrable (fun y => ‖M (z*v) y-interpolation (probabilityNodes n)
        (fun i => M (z*probabilityNodes n i) y) v‖^2) (gibbs (centeringPotential F x r T)) ∧
      (∫y,‖M (z*v) y-interpolation (probabilityNodes n)
        (fun i => M (z*probabilityNodes n i) y) v‖^2 ∂gibbs (centeringPotential F x r T))≤
        4*C^2*(z^(n+1)/(n.factorial:ℝ))^2*
          ((d*((lam:ℝ)*r)^2)*(R⁻¹)^(4*(n+1))*harmonicMeanBudget (n+1)) := by
  obtain ⟨C,hC,hC'⟩ := exists_basis_budget (probabilityNodes n)
  refine ⟨C,hC,?_⟩
  intro d F lam hF x r R T hr hlam hl hR hRT hT0 hT1 Ξ hder hm hlaw z hz hz1 v hv M
  let J := fun k s y => tensorVector (iterTensorLie (centeringPotential F x r T)
    (harmonicSkew d) (centeringMeanArray F x r T) k) (Ξ y s)
  have hH : PolySmooth (centeringPotential F x r T) := productPotential_polySmooth
    (interpolationPotential_polySmooth hF x hr hlam hl hT0 hT1) (gaussianPotential_polySmooth d)
  have hJ (k : ℕ) (s : ℝ) : Measurable (J k s) :=
    liePathJet_measurable hH (harmonicSkew d) (centeringMeanArray F x r T)
      (harmonicSkew_polySmooth d) (centeringMeanArray_polySmooth hF x hr hlam hl hT0 hT1) Ξ hm k s
  have hs (s : ℝ) (hs : s∈insert v (range (probabilityNodes n))) : s∈Icc (0:ℝ) 1 := by
    rcases hs with he|⟨i,rfl⟩
    · simpa only [he] using hv
    · exact probabilityNodes_mem hn i
  have hsz (s : ℝ) (hs' : s∈insert v (range (probabilityNodes n))) : 0≤z*s ∧ z*s≤z :=
    ⟨mul_nonneg hz (hs s hs').1,mul_le_of_le_one_right hz (hs s hs').2⟩
  have htay (s : ℝ) (hs' : s∈insert v (range (probabilityNodes n))) :=
    harmonic_mean_taylor_uniform hF x hr hlam hl hR hRT hT0 hT1 Ξ hder hm hlaw n 0 (z*s)
      le_rfl (hsz s hs').1 ((hsz s hs').2.trans hz1)
  have h := cell_chain_error_rms (probabilityNodes n) (probabilityNodes_injective hn) n
    (by simp) J 0 z v
    (B:=(z^(n+1)/(n.factorial:ℝ))^2*((d*((lam:ℝ)*r)^2)*(R⁻¹)^(4*(n+1))*harmonicMeanBudget (n+1)))
    (by positivity [harmonicMeanBudget_nonneg (n+1)]) hC (hC' v hv)
    (fun s _ => ((hJ 0 _).sub (chainTaylor_measurable J hJ n 0 _)).aestronglyMeasurable)
    (fun s hs' => by simpa only [zero_add,sub_zero,J,iterTensorLie] using (htay s hs').1)
    (fun s hs' => by
      have hh := (htay s hs').2
      change (∫y,‖J 0 (z*s) y-chainTaylor (fun k v => J k v y) n 0 (z*s)‖^2 ∂gibbs (centeringPotential F x r T))≤_ at hh
      simp only [zero_add]
      apply hh.trans
      simp only [sub_zero]
      apply mul_le_mul_of_nonneg_right _ (by positivity [harmonicMeanBudget_nonneg (n+1)])
      apply pow_le_pow_left₀ (div_nonneg (pow_nonneg (hsz s hs').1 _) (Nat.cast_nonneg _))
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact pow_le_pow_left₀ (hsz s hs').1 (hsz s hs').2 _)
  simpa only [zero_add,J,iterTensorLie,M,mul_assoc] using h
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory TensorEnergy Quadrature
open scoped Classical BigOperators NNReal RealInnerProductSpace

local instance : DecidableEq Unit := Classical.decEq _

def finiteCoordinateProjection {I J : Type*} [Fintype I] [Fintype J]
    (e : I ↪ J) : EuclideanSpace ℝ J →L[ℝ] EuclideanSpace ℝ I :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : I => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => PiLp.proj 2 (fun _ : J => ℝ) (e i)))

lemma finiteCoordinateProjection_norm_le {I J : Type*} [Fintype I] [Fintype J]
    (e : I ↪ J) (v : EuclideanSpace ℝ J) : ‖finiteCoordinateProjection e v‖≤‖v‖ := by
  have he : ‖finiteCoordinateProjection e v‖^2≤‖v‖^2 := by
    rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
    change (∑i : I,(v (e i))^2)≤∑j : J,(v j)^2
    calc
      _ = ∑j∈Finset.univ.map e,(v j)^2 := by rw [Finset.sum_map]
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun j _ _ => sq_nonneg _)
  nlinarith [norm_nonneg (finiteCoordinateProjection e v),norm_nonneg v]

def meanOutputEmbedding (d : ℕ) : Fin d ↪ (Unit → Fin (d+d)) :=
  ⟨fun i _ => leftCoordinates d d i,fun _ _ h => (leftCoordinates d d).injective (congrFun h ())⟩

def meanOutputProjection (d : ℕ) : EuclideanSpace ℝ (Unit → Fin (d+d)) →L[ℝ] Point d :=
  finiteCoordinateProjection (meanOutputEmbedding d)

lemma meanOutputProjection_mean {d : ℕ} (F : Point d → ℝ) (x : Point d) (r T : ℝ)
    (y : Point (d+d)) : meanOutputProjection d (tensorVector (centeringMeanArray F x r T) y)=
      conditionalFieldMean F x r T (productPointEquiv d d y).1 := by
  ext i
  change TensorEnergy.zeroExtend (slotEmbedding (fun _ : Unit => leftCoordinates d d))
    (fun a => conditionalMeanArray F x r T a (coordinateProjection (leftCoordinates d d) y))
    (slotEmbedding (fun _ : Unit => leftCoordinates d d) (fun _ => i))=_
  rw [zeroExtend_apply,coordinateProjection_left]
  simp only [conditionalMeanArray,EuclideanSpace.basisFun_inner]

lemma projection_interpolation {I E G : Type*} [Fintype I] [DecidableEq I]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (L : E →L[ℝ] G) (u : I → ℝ) (v : I → E) (t : ℝ) :
    L (interpolation u v t)=interpolation u (fun i => L (v i)) t := by
  simp only [interpolation,map_sum,map_smul]

theorem harmonic_point_interpolation_rms (n : ℕ) (hn : 0<n) :
    ∃C : ℝ,1≤C ∧ ∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},
      ∀_ : Primitive F lam,∀(x : Point d) {r R T : ℝ},
      0<r → 0<lam → (lam:ℝ)*r^2≤1/2 → 0<R → R^2≤1-T^2 → 0≤T → T<1 →
      ∀Ξ : Point (d+d) → ℝ → Point (d+d),
      (∀y v,v∈Icc (0:ℝ) 1 → HasDerivWithinAt (Ξ y)
        (skewLieField (centeringPotential F x r T) (harmonicSkew d) (Ξ y v)) (Icc (0:ℝ) 1) v) →
      Measurable (fun p : ℝ × Point (d+d) => Ξ p.2 p.1) →
      (∀v∈Icc (0:ℝ) 1,(gibbs (centeringPotential F x r T)).map (fun y => Ξ y v)=
        gibbs (centeringPotential F x r T)) →
      ∀z : ℝ,0≤z → z≤1 → ∀v∈Icc (0:ℝ) 1,
      let M := fun s y => conditionalFieldMean F x r T (productPointEquiv d d (Ξ y s)).1
      Integrable (fun y => ‖M (z*v) y-interpolation (probabilityNodes n)
        (fun i => M (z*probabilityNodes n i) y) v‖^2) (gibbs (centeringPotential F x r T)) ∧
      (∫y,‖M (z*v) y-interpolation (probabilityNodes n)
        (fun i => M (z*probabilityNodes n i) y) v‖^2 ∂gibbs (centeringPotential F x r T))≤
        4*C^2*(z^(n+1)/(n.factorial:ℝ))^2*
          ((d*((lam:ℝ)*r)^2)*(R⁻¹)^(4*(n+1))*harmonicMeanBudget (n+1)) := by
  obtain ⟨C,hC,hC'⟩ := harmonic_mean_interpolation_rms n hn
  refine ⟨C,hC,?_⟩
  intro d F lam hF x r R T hr hlam hl hR hRT hT0 hT1 Ξ hder hm hlaw z hz hz1 v hv M
  let Q := fun s y => tensorVector (centeringMeanArray F x r T) (Ξ y s)
  let E := fun y => Q (z*v) y-interpolation (probabilityNodes n)
    (fun i => Q (z*probabilityNodes n i) y) v
  have hb := hC' hF x hr hlam hl hR hRT hT0 hT1 Ξ hder hm hlaw z hz hz1 v hv
  have he (y : Point (d+d)) : M (z*v) y-interpolation (probabilityNodes n)
      (fun i => M (z*probabilityNodes n i) y) v=meanOutputProjection d (E y) := by
    simp only [E,map_sub,Q,projection_interpolation,meanOutputProjection_mean,M]
  have hQ (s : ℝ) : Measurable (Q s) :=
    (tensorVector_contDiff _ (fun c =>
      (centeringMeanArray_polySmooth hF x hr hlam hl hT0 hT1 c).smooth)).continuous.measurable.comp
      (hm.comp (measurable_const.prodMk measurable_id))
  have hE : Measurable E := (hQ _).sub
    (Finset.measurable_sum _ (fun i _ => by
      change Measurable (fun y => basis (probabilityNodes n) i v • Q (z*probabilityNodes n i) y)
      exact (hQ _).const_smul (basis (probabilityNodes n) i v)))
  have hab (y : Point (d+d)) : ‖meanOutputProjection d (E y)‖^2≤‖E y‖^2 :=
    pow_le_pow_left₀ (norm_nonneg _) (finiteCoordinateProjection_norm_le _ _) 2
  simp_rw [he]
  have hi := hb.1.mono' (((meanOutputProjection d).continuous.measurable.comp hE).norm.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun y => by simpa only [Real.norm_eq_abs,abs_sq,Function.comp_def,E,Q] using hab y))
  exact ⟨hi,(integral_mono hi hb.1 hab).trans hb.2⟩
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature
open scoped Classical BigOperators

abbrev ProbabilityNode (T h : ℝ) (n : ℕ) := Fin (logMeshCount T h) × Fin (n+1)

def probabilityCellLength (T h : ℝ) (c : Fin (logMeshCount T h)) : ℝ :=
  logMeshNode T h (c.val+1)-logMeshNode T h c.val

def probabilityNodeTime (T h : ℝ) (n : ℕ) (i : ProbabilityNode T h n) : ℝ :=
  logMeshNode T h i.1.val+probabilityCellLength T h i.1*probabilityNodes n i.2

def probabilityWeight (T h : ℝ) (n : ℕ) : ProbabilityNode T h n → ProbabilityNode T h n → ℝ :=
  compositeWeight (probabilityNodes n) (probabilityCellLength T h)

lemma probabilityCellLength_pos {T h : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    (c : Fin (logMeshCount T h)) : 0<probabilityCellLength T h c :=
  sub_pos.mpr (logMeshNode_strictMono hT0 hT1 hh (Nat.lt_succ_self _))

lemma probabilityCellLength_sum {T h : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0<h) :
    (∑c,probabilityCellLength T h c)=T := by
  unfold probabilityCellLength
  rw [Fin.sum_univ_eq_sum_range (fun j => logMeshNode T h (j+1)-logMeshNode T h j),
    Finset.sum_range_sub,logMeshNode_last hT0 hT1 hh,
    logMeshNode_zero,sub_zero]

lemma probabilityNodeTime_mem {T h : ℝ} (hT0 : 0<T) (hT1 : T<1) (hh : 0<h)
    {n : ℕ} (hn : 0<n) (i : ProbabilityNode T h n) : probabilityNodeTime T h n i∈Icc 0 T := by
  have ha := logMeshNode_mem hT0 hT1 hh i.1.2.le
  have hb := logMeshNode_mem hT0 hT1 hh (Nat.succ_le_of_lt i.1.2)
  have hu := probabilityNodes_mem hn i.2
  have hl := (probabilityCellLength_pos hT0 hT1 hh i.1).le
  have hc := mul_le_mul_of_nonneg_left hu.2 hl
  have h0 := mul_nonneg hl hu.1
  dsimp only [probabilityNodeTime,probabilityCellLength] at *
  rcases ha with ⟨ha0,haT⟩
  rcases hb with ⟨hb0,hbT⟩
  simp only [Nat.succ_eq_add_one,mul_one] at hbT hc
  constructor <;> linarith

lemma probabilityWeight_budget (n : ℕ) (hn : 0<n) :
    ∃A : ℝ,0≤A ∧ ∀{T h : ℝ},0<T → T<1 → 0<h →
      ∀i : ProbabilityNode T h n,∑j,|probabilityWeight T h n i j|≤A := by
  obtain ⟨C,hC,hC'⟩ := exists_basis_budget (probabilityNodes n)
  refine ⟨(Fintype.card (Fin (n+1)):ℝ)*C,by positivity,?_⟩
  intro T h hT0 hT1 hh i
  exact compositeWeight_budget (probabilityNodes_mem hn)
    (fun c => (probabilityCellLength_pos hT0 hT1 hh c).le)
    (by rw [probabilityCellLength_sum hT0 hT1 hh]; exact hT1.le)
    (by linarith) hC' i

lemma probabilityNode_card (T h : ℝ) (n : ℕ) :
    Fintype.card (ProbabilityNode T h n)=logMeshCount T h*(n+1) := by
  simp [ProbabilityNode]
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature FinitePicard
open scoped Classical BigOperators NNReal

def probabilityMeanVelocity {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (r t : ℝ) (y : Point d) : Point d := -r • conditionalFieldMean F x r t y

def probabilityMeanLipschitz (lam : ℝ≥0) (r : ℝ) : ℝ≥0 :=
  ⟨(Real.pi^2/2)*(lam:ℝ)*r^2,by positivity⟩

lemma probabilityMeanVelocity_lipschitz {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r t : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (ht0 : 0≤t) (ht1 : t<1) :
    LipschitzWith (probabilityMeanLipschitz lam r) (probabilityMeanVelocity F x r t) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  have he := (conditionalFieldMean_lipschitz hF x hr hl ht0 ht1).dist_le_mul y z
  simp only [probabilityMeanVelocity,dist_smul₀,Real.norm_eq_abs,abs_neg,abs_of_nonneg hr,
    probabilityMeanLipschitz]
  have hh := mul_le_mul_of_nonneg_left he hr
  have hp : 0≤(Real.pi^2/2)*(lam:ℝ)*r^2*dist y z := by positivity
  calc
    _ ≤ r*((Real.pi^2/2)*t*((lam:ℝ)*r)*dist y z) := hh
    _ = t*((Real.pi^2/2)*(lam:ℝ)*r^2*dist y z) := by ring
    _ ≤ _ := mul_le_of_le_one_left hp ht1.le

def probabilityPicard {d : ℕ} (F : Point d → ℝ) (x : Point d)
    (r T h : ℝ) (n N : ℕ) : Point d → ProbabilityNode T h n → Point d :=
  nodes (probabilityWeight T h n)
    (fun j => probabilityMeanVelocity F x r (probabilityNodeTime T h n j))
    (fun y _ => y) N

lemma probabilityConstantPath_lipschitz {d : ℕ} (T h : ℝ) (n : ℕ) :
    LipschitzWith 1 (fun y : Point d => fun _ : ProbabilityNode T h n => y) := by
  apply LipschitzWith.of_dist_le_mul
  intro y z
  apply (dist_pi_le_iff (by positivity)).mpr
  intro i
  simp

theorem probabilityPicard_lipschitz (n : ℕ) (hn : 0<n) :
    ∃A : ℝ≥0,∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},
      Primitive F lam → ∀(x : Point d) {r T h : ℝ},0≤r →
        (lam:ℝ)*r^2≤1/2 → 0<T → T<1 → 0<h →
        A*probabilityMeanLipschitz lam r≤1/2 → ∀N : ℕ,
      LipschitzWith 2 (probabilityPicard F x r T h n N) ∧
      LipschitzWith (2*(A*probabilityMeanLipschitz lam r))
        (fun y => probabilityPicard F x r T h n (N+1) y-(fun _ => y)) := by
  obtain ⟨A,hA,hA'⟩ := probabilityWeight_budget n hn
  refine ⟨⟨A,hA⟩,?_⟩
  intro d F lam hF x r T h hr hl hT0 hT1 hh hq N
  have hφ (j : ProbabilityNode T h n) := probabilityMeanVelocity_lipschitz hF x hr hl
    (probabilityNodeTime_mem hT0 hT1 hh hn j).1
    ((probabilityNodeTime_mem hT0 hT1 hh hn j).2.trans_lt hT1)
  have hw := hA' hT0 hT1 hh
  constructor
  · apply LipschitzWith.of_dist_le_mul
    intro y z
    have he := (nodes_lipschitz (A:=⟨A,hA⟩) (K:=probabilityMeanLipschitz lam r) (probabilityWeight T h n)
      (fun j => probabilityMeanVelocity F x r (probabilityNodeTime T h n j))
      (fun y : Point d => fun _ => y) hw hφ (probabilityConstantPath_lipschitz T h n) hq N).dist_le_mul y z
    simpa only [probabilityPicard,NNReal.coe_mul,NNReal.coe_ofNat,NNReal.coe_one,mul_one,dist_eq_norm] using he
  · apply LipschitzWith.of_dist_le_mul
    intro y z
    have he := (nodes_correction_lipschitz (A:=⟨A,hA⟩) (K:=probabilityMeanLipschitz lam r) (probabilityWeight T h n)
      (fun j => probabilityMeanVelocity F x r (probabilityNodeTime T h n j))
      (fun y : Point d => fun _ => y) hw hφ (probabilityConstantPath_lipschitz T h n) hq N).dist_le_mul y z
    convert he using 1 <;> simp only [probabilityPicard,NNReal.coe_mul,NNReal.coe_ofNat,mul_one,dist_eq_norm]
    ring

def probabilityMeanCalls (T h : ℝ) (n N : ℕ) : ℕ := N*(logMeshCount T h*(n+1))

lemma probabilityMeanCalls_succ (T h : ℝ) (n N : ℕ) :
    probabilityMeanCalls T h n (N+1)=probabilityMeanCalls T h n N+
      Fintype.card (ProbabilityNode T h n) := by
  rw [probabilityNode_card]
  unfold probabilityMeanCalls
  ring
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open Set MeasureTheory Quadrature FinitePicard
open scoped Classical BigOperators NNReal

def harmonicWeight (n : ℕ) (z : ℝ) (i j : Fin (n+1)) : ℝ :=
  z*(∫v in 0..probabilityNodes n i,
    Real.sin (z*(probabilityNodes n i-v))*basis (probabilityNodes n) j v)

lemma harmonicWeight_budget (n : ℕ) (hn : 0<n) :
    ∃A : ℝ≥0,∀z : ℝ,0≤z → z≤1 → ∀i,∑j,|harmonicWeight n z i j|≤A := by
  obtain ⟨C,hC,hC'⟩ := exists_basis_budget (probabilityNodes n)
  have hC0 : 0≤C := by linarith
  refine ⟨⟨(n+1:ℕ)*C,by positivity⟩,?_⟩
  intro z hz hz1 i
  have hi := probabilityNodes_mem hn i
  have hb (j : Fin (n+1)) : |harmonicWeight n z i j|≤C := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a:=0) (b:=probabilityNodes n i)
      (f:=fun v => Real.sin (z*(probabilityNodes n i-v))*basis (probabilityNodes n) j v)
      (C:=C) (fun v hv => by
        rw [uIoc_of_le hi.1] at hv
        rw [norm_mul,Real.norm_eq_abs,Real.norm_eq_abs]
        have he := (Finset.single_le_sum (fun k _ => abs_nonneg (basis (probabilityNodes n) k v))
          (Finset.mem_univ j)).trans (hC' v ⟨hv.1.le,hv.2.trans hi.2⟩)
        exact (mul_le_mul_of_nonneg_right (Real.abs_sin_le_one _) (abs_nonneg _)).trans
          (by simpa only [one_mul] using he))
    rw [sub_zero,abs_of_nonneg hi.1] at hh
    dsimp only [harmonicWeight]
    rw [abs_mul,abs_of_nonneg hz]
    have hh' : |∫v in 0..probabilityNodes n i,
        Real.sin (z*(probabilityNodes n i-v))*basis (probabilityNodes n) j v|≤C*probabilityNodes n i := by
      simpa only [Real.norm_eq_abs] using hh
    have he : |∫v in 0..probabilityNodes n i,
        Real.sin (z*(probabilityNodes n i-v))*basis (probabilityNodes n) j v|≤C :=
      hh'.trans (mul_le_of_le_one_right hC0 hi.2)
    exact (mul_le_mul_of_nonneg_left he hz).trans (mul_le_of_le_one_left hC0 hz1)
  calc
    _ ≤ ∑j : Fin (n+1),C := Finset.sum_le_sum (fun j _ => hb j)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; norm_cast

def harmonicFree {d : ℕ} (n : ℕ) (z : ℝ) (p : Point d × Point d) : Fin (n+1) → Point d :=
  fun i => Real.cos (z*probabilityNodes n i) • p.1+Real.sin (z*probabilityNodes n i) • p.2

lemma harmonicFree_lipschitz {d : ℕ} (n : ℕ) (z : ℝ) :
    LipschitzWith 2 (harmonicFree (d:=d) n z) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  apply (dist_pi_le_iff (by positivity)).mpr
  intro i
  have he := (((lipschitzWith_smul (Real.cos (z*probabilityNodes n i))).comp
    (LipschitzWith.prod_fst (α:=Point d) (β:=Point d))).add
    ((lipschitzWith_smul (Real.sin (z*probabilityNodes n i))).comp
      (LipschitzWith.prod_snd (α:=Point d) (β:=Point d)))).dist_le_mul p q
  have hc : ‖Real.cos (z*probabilityNodes n i)‖+‖Real.sin (z*probabilityNodes n i)‖≤2 := by
    have hc := add_le_add (Real.abs_cos_le_one (z*probabilityNodes n i)) (Real.abs_sin_le_one (z*probabilityNodes n i))
    simpa only [Real.norm_eq_abs,show (1:ℝ)+1=2 by norm_num] using hc
  change dist (harmonicFree n z p i) (harmonicFree n z q i)≤_ at he
  simp only [NNReal.coe_add,mul_one,coe_nnnorm] at he
  exact he.trans (mul_le_mul_of_nonneg_right hc dist_nonneg)

def harmonicMeanVelocity {d : ℕ} (F : Point d → ℝ) (x : Point d) (r ρ : ℝ) (y : Point d) : Point d :=
  ρ • probabilityMeanVelocity F x r ρ y

lemma harmonicMeanVelocity_lipschitz {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r ρ : ℝ} (hr : 0≤r)
    (hl : (lam:ℝ)*r^2≤1/2) (hρ0 : 0≤ρ) (hρ1 : ρ<1) :
    LipschitzWith (probabilityMeanLipschitz lam r) (harmonicMeanVelocity F x r ρ) := by
  apply ((lipschitzWith_smul ρ).comp (probabilityMeanVelocity_lipschitz hF x hr hl hρ0 hρ1)).weaken
  change ‖ρ‖*(probabilityMeanLipschitz lam r:ℝ)≤_
  rw [Real.norm_eq_abs,abs_of_nonneg hρ0]
  exact mul_le_of_le_one_left (probabilityMeanLipschitz lam r).2 hρ1.le

def harmonicPicard {d : ℕ} (F : Point d → ℝ) (x : Point d) (r ρ z : ℝ) (n N : ℕ) :
    Point d × Point d → Fin (n+1) → Point d :=
  nodes (harmonicWeight n z) (fun _ => harmonicMeanVelocity F x r ρ) (harmonicFree n z) N

theorem harmonicPicard_lipschitz (n : ℕ) (hn : 0<n) :
    ∃A : ℝ≥0,∀{d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0},
      Primitive F lam → ∀(x : Point d) {r ρ z : ℝ},0≤r →
        (lam:ℝ)*r^2≤1/2 → 0≤ρ → ρ<1 → 0≤z → z≤1 →
        A*probabilityMeanLipschitz lam r≤1/2 → ∀N : ℕ,
      LipschitzWith 4 (harmonicPicard F x r ρ z n N) ∧
      LipschitzWith (4*(A*probabilityMeanLipschitz lam r))
        (fun p => harmonicPicard F x r ρ z n (N+1) p-harmonicFree n z p) := by
  obtain ⟨A,hA⟩ := harmonicWeight_budget n hn
  refine ⟨A,?_⟩
  intro d F lam hF x r ρ z hr hl hρ0 hρ1 hz hz1 hq N
  have hφ := harmonicMeanVelocity_lipschitz hF x hr hl hρ0 hρ1
  constructor
  · simpa only [harmonicPicard,show (2:ℝ≥0)*2=4 by norm_num] using
      nodes_lipschitz (harmonicWeight n z) (fun _ => harmonicMeanVelocity F x r ρ)
        (harmonicFree n z) (hA z hz hz1) (fun _ => hφ) (harmonicFree_lipschitz n z) hq N
  · have hh := nodes_correction_lipschitz (harmonicWeight n z) (fun _ => harmonicMeanVelocity F x r ρ)
        (harmonicFree n z) (hA z hz hz1) (fun _ => hφ) (harmonicFree_lipschitz n z) hq N
    convert hh using 1 <;> first | rfl | ring

def harmonicMeanCalls (n N : ℕ) : ℕ := N*(n+1)

lemma harmonicMeanCalls_succ (n N : ℕ) :
    harmonicMeanCalls n (N+1)=harmonicMeanCalls n N+Fintype.card (Fin (n+1)) := by
  simp only [harmonicMeanCalls,Fintype.card_fin]
  ring
end LogConcaveSampling

end

end

section

noncomputable section
namespace LogConcaveSampling
open MeasureTheory Set Quadrature
open scoped BigOperators

variable {E Ω : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace Ω] {ν : Measure Ω} [SFinite ν]

lemma harmonicWeight_sum_integral (n : ℕ) (z : ℝ) (i : Fin (n+1)) (v : Fin (n+1) → E) :
    (∑j,harmonicWeight n z i j • v j)=z • (∫t in 0..probabilityNodes n i,
      Real.sin (z*(probabilityNodes n i-t)) • interpolation (probabilityNodes n) v t) := by
  simp_rw [interpolation,Finset.smul_sum,smul_smul]
  rw [intervalIntegral.integral_finsetSum]
  · rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [intervalIntegral.integral_smul_const]
    simp only [harmonicWeight,smul_smul]
  · intro j hj
    exact ((Real.continuous_sin.comp
      (continuous_const.mul (continuous_const.sub continuous_id))).mul
      (basis_continuous (probabilityNodes n) j)).smul continuous_const |>.intervalIntegrable _ _

theorem harmonic_quadrature_error_rms (n : ℕ) (z : ℝ) (i : Fin (n+1))
    (f : ℝ → Ω → E) (hi0 : 0≤probabilityNodes n i) {B : ℝ} (hB0 : 0≤B)
    (hf : ∀y,Continuous (fun t => f t y))
    (hm : AEStronglyMeasurable (fun p : ℝ × Ω => f p.1 p.2-
      interpolation (probabilityNodes n) (fun j => f (probabilityNodes n j) p.2) p.1)
      ((volume.restrict (Ioc 0 (probabilityNodes n i))).prod ν))
    (hi : ∀t∈Ioc 0 (probabilityNodes n i),Integrable (fun y => ‖f t y-
      interpolation (probabilityNodes n) (fun j => f (probabilityNodes n j) y) t‖^2) ν)
    (hB : ∀t∈Ioc 0 (probabilityNodes n i),(∫y,‖f t y-
      interpolation (probabilityNodes n) (fun j => f (probabilityNodes n j) y) t‖^2 ∂ν)≤B) :
    Integrable (fun y => ‖z • (∫t in 0..probabilityNodes n i,
      Real.sin (z*(probabilityNodes n i-t)) • f t y)-
      ∑j,harmonicWeight n z i j • f (probabilityNodes n j) y‖^2) ν ∧
    (∫y,‖z • (∫t in 0..probabilityNodes n i,
      Real.sin (z*(probabilityNodes n i-t)) • f t y)-
      ∑j,harmonicWeight n z i j • f (probabilityNodes n j) y‖^2 ∂ν)≤
      z^2*(probabilityNodes n i)^2*B := by
  let μ : Measure ℝ := volume.restrict (Ioc 0 (probabilityNodes n i))
  let w : ℝ → ℝ := fun t => Real.sin (z*(probabilityNodes n i-t))
  have hw : Continuous w := by dsimp [w]; fun_prop
  have hs : ∀ᵐ t ∂μ,Integrable (fun y => ‖f t y-
      interpolation (probabilityNodes n) (fun j => f (probabilityNodes n j) y) t‖^2) ν := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hi t ht
  have hb : ∀ᵐ t ∂μ,(∫y,‖f t y-
      interpolation (probabilityNodes n) (fun j => f (probabilityNodes n j) y) t‖^2 ∂ν)≤B := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact hB t ht
  have hv := RMSIntegral.weighted_time_seed hm hw.aestronglyMeasurable hB0
    (Filter.Eventually.of_forall (fun t => Real.abs_sin_le_one (z*(probabilityNodes n i-t)))) hs hb
  have he (y : Ω) : z • (∫t in 0..probabilityNodes n i,w t • f t y)-
      ∑j,harmonicWeight n z i j • f (probabilityNodes n j) y=
      z • (∫t,w t • (f t y-interpolation (probabilityNodes n)
        (fun j => f (probabilityNodes n j) y) t) ∂μ) := by
    rw [harmonicWeight_sum_integral,←smul_sub]
    change z • ((∫t in 0..probabilityNodes n i,w t • f t y)-
      ∫t in 0..probabilityNodes n i,w t • interpolation (probabilityNodes n)
        (fun j => f (probabilityNodes n j) y) t)=_
    rw [←intervalIntegral.integral_sub (f:=fun t => w t • f t y)
      (g:=fun t => w t • interpolation (probabilityNodes n) (fun j => f (probabilityNodes n j) y) t)
      ((hw.smul (hf y)).intervalIntegrable _ _)
      ((hw.smul (interpolation_continuous _ _)).intervalIntegrable _ _)]
    simp_rw [←smul_sub]
    rw [intervalIntegral.integral_of_le hi0]
  have hnorm (v : E) : ‖z • v‖^2=z^2*‖v‖^2 := by
    rw [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
  dsimp only [w] at he
  simp_rw [he,hnorm]
  refine ⟨hv.1.const_mul (z^2),?_⟩
  rw [integral_const_mul]
  have hμ : μ.real univ=probabilityNodes n i := by
    dsimp only [μ,Measure.real]
    rw [Measure.restrict_apply_univ]
    change volume.real (Ioc 0 (probabilityNodes n i))=probabilityNodes n i
    rw [Real.volume_real_Ioc_of_le hi0,sub_zero]
  rw [hμ,one_pow,mul_one] at hv
  exact (mul_le_mul_of_nonneg_left hv.2 (sq_nonneg z)).trans_eq (by ring)
end LogConcaveSampling

end

end

end

end OAI
