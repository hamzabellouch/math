import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.WeightedBoxes01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
section
section
open scoped BigOperators ENNReal
open MvPolynomial

 
end

section
 

noncomputable section
namespace RationalLattice
open WeightedPolynomial MalcevCharacters
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n : ℕ} (c : RealCoordinates G n) (hsk : SecondKind c)
variable (H : CubeFaces.Filtration G) (w : Fin n → ℕ) (hw : ∀ i,0 < w i)
variable (hmono : Monotone w)
variable (hH : ∀ k (g : G),g∈H.level k ↔ ∀ i : Fin n,w i < k → c.coord g i=0)
variable (F : G →* G) (hF : Continuous F)
variable (hd : ∀ k,0 < k → ∀ g∈H.level k,g⁻¹*F g∈H.level (k+1))

include hsk hw hmono hH hF hd in
lemma logHomLinear_displacement_weighted (i : Fin n) :
    IsWeighted w (w i-1) (fun x=>(logHomLinear c c F x-x) i) := by
  let A : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    (LinearMap.proj i).comp ((logHomLinear c c F).toLinearMap-LinearMap.id)
  change IsWeighted w (w i-1) A
  apply IsWeighted.linear
  intro j hj
  change (logHomLinear c c F (Pi.single j (1:ℝ)) i)-(Pi.single j (1:ℝ) : Fin n → ℝ) i=0
  apply logHomLinear_lowers_of_displacement c H w hmono hH hsk F hF (w j)
    (hd (w j) (hw j)) (Pi.single j 1)
  · intro l hl
    apply Pi.single_eq_of_ne
    intro he
    subst l
    exact (lt_irrefl _ hl)
  · omega

include hsk hw hmono hH hF hd in
lemma logHomLinear_weighted (i : Fin n) :
    IsWeighted w (w i) (fun x=>logHomLinear c c F x i) := by
  have hs := ((logHomLinear_displacement_weighted c hsk H w hw hmono hH F hF hd i).mono
    (Nat.sub_le _ _)).add (IsWeighted.coordinate w i)
  simpa only [Pi.sub_apply,sub_add_cancel] using hs

include hsk hw hmono hH hF hd in
 

theorem affine_log_displacement_weighted (a : G) (i : Fin n) :
    IsWeighted w (w i-1) (fun y=>canonicalLog c (a*F (canonicalExp c y)) i-y i) := by
  have h₁:=IsWeighted.comp (log_left_displacement_weighted c hsk H w hH hw a i)
    (fun j=>logHomLinear_weighted c hsk H w hw hmono hH F hF hd j)
  have h₂:=logHomLinear_displacement_weighted c hsk H w hw hmono hH F hF hd i
  have he (y : Fin n → ℝ) :
      canonicalExp c (logHomLinear c c F y)=F (canonicalExp c y) := by
    rw [logHomLinear_apply c c hsk F hF]
    exact canonicalExp_log c _
  simpa only [Function.comp_apply,he,Pi.sub_apply,sub_add_sub_cancel] using h₁.add h₂

end RationalLattice
end
 
end

section
 

noncomputable section
open scoped BigOperators
namespace WeightedLinear
variable {σ τ : Type*} [Fintype σ] [Fintype τ] [DecidableEq σ] [DecidableEq τ]

 
def level (w : σ → ℕ) (k : ℕ) : Submodule ℝ (σ → ℝ) where
  carrier := {x | ∀ i,w i < k → x i=0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy i hi; simp [hx i hi,hy i hi]
  smul_mem' := by intro a x hx i hi; simp [hx i hi]

def Preserves (w : σ → ℕ) (v : τ → ℕ) (p : (σ → ℝ) →ₗ[ℝ] (τ → ℝ)) : Prop :=
  ∀ k ⦃x⦄,x ∈ level w k → p x ∈ level v k

omit [Fintype σ] in
lemma single_mem (w : σ → ℕ) (i : σ) : Pi.single i (1:ℝ) ∈ level w (w i) := by
  intro j hj
  apply Pi.single_eq_of_ne
  rintro rfl
  exact (lt_irrefl _ hj)

lemma basis_expansion (x : σ → ℝ) : x=∑ i : σ,x i • Pi.single i 1 := by
  ext j
  simp [Finset.sum_apply,Pi.smul_apply,Pi.single_apply]

omit [Fintype τ] [DecidableEq τ] in
lemma apply_eq_sum (p : (σ → ℝ) →ₗ[ℝ] (τ → ℝ)) (x : σ → ℝ) (j : τ) :
    p x j=∑ i : σ,p (Pi.single i 1) j*x i := by
  conv_lhs => rw [basis_expansion x,map_sum]
  simp only [Finset.sum_apply,map_smul,Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i hi
  exact mul_comm _ _

omit [Fintype σ] [Fintype τ] [DecidableEq τ] in
lemma Preserves.coeff {w : σ → ℕ} {v : τ → ℕ}
    {p : (σ → ℝ) →ₗ[ℝ] (τ → ℝ)} (hp : Preserves w v p)
    (i : σ) (j : τ) (hij : v j < w i) : p (Pi.single i 1) j=0 :=
  hp (w i) (single_mem w i) j hij

omit [Fintype τ] [DecidableEq τ] in
lemma preserves_of_coeff {w : σ → ℕ} {v : τ → ℕ}
    {p : (σ → ℝ) →ₗ[ℝ] (τ → ℝ)}
    (hp : ∀ i j,v j < w i → p (Pi.single i 1) j=0) : Preserves w v p := by
  intro k x hx j hj
  rw [apply_eq_sum]
  apply Finset.sum_eq_zero
  intro i hi
  by_cases hik : w i < k
  · rw [hx i hik,mul_zero]
  · rw [hp i j (by omega),zero_mul]

omit [Fintype τ] [DecidableEq τ] in
lemma Preserves.weighted {w : σ → ℕ} {v : τ → ℕ}
    {p : (σ → ℝ) →ₗ[ℝ] (τ → ℝ)} (hp : Preserves w v p) (j : τ) :
    WeightedPolynomial.IsWeighted w (v j) (fun x=>p x j) := by
  exact WeightedPolynomial.IsWeighted.linear w (v j) ((LinearMap.proj j).comp p)
    (fun i hi=>hp.coeff i j hi)

 
omit [Fintype σ] [DecidableEq σ] in
theorem exists_rightInverse (w : σ → ℕ) (v : τ → ℕ)
    (p : (σ → ℝ) →ₗ[ℝ] (τ → ℝ))
    (honto : ∀ k,Submodule.map p (level w k)=level v k) :
    ∃ R : (τ → ℝ) →ₗ[ℝ] (σ → ℝ),
      (∀ y,p (R y)=y) ∧ Preserves v w R := by
  have hex (j : τ) : ∃ x∈level w (v j),p x=Pi.single j 1 := by
    apply Submodule.mem_map.mp
    rw [honto]
    exact single_mem v j
  choose b hb hpb using hex
  let R : (τ → ℝ) →ₗ[ℝ] (σ → ℝ) :=
    ∑ j : τ,(LinearMap.proj j).smulRight (b j)
  have hR (y : τ → ℝ) : R y=∑ j : τ,y j • b j := by
    simp [R,LinearMap.sum_apply]
  refine ⟨R,?_,?_⟩
  · intro y
    rw [hR,map_sum]
    simp only [map_smul,hpb]
    exact (basis_expansion y).symm
  · intro k y hy i hi
    rw [hR]
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
    apply Finset.sum_eq_zero
    intro j hj
    by_cases hjk : v j < k
    · rw [hy j hjk,zero_mul]
    · rw [hb j i (by omega),mul_zero]

 

theorem lifted_displacement_weighted {w : σ → ℕ} {v : τ → ℕ}
    {p : (σ → ℝ) →ₗ[ℝ] (τ → ℝ)} {R : (τ → ℝ) →ₗ[ℝ] (σ → ℝ)}
    (hp : Preserves w v p) (hR : Preserves v w R)
    (D : (τ → ℝ) → (τ → ℝ))
    (hD : ∀ j,WeightedPolynomial.IsWeighted v (v j-1) (fun y=>D y j)) (i : σ) :
    WeightedPolynomial.IsWeighted w (w i-1) (fun x=>R (D (p x)) i) := by
  have hsum : WeightedPolynomial.IsWeighted w (w i-1)
      (fun x=>∑ j : τ,R (Pi.single j 1) i*D (p x) j) := by
    apply WeightedPolynomial.IsWeighted.sum
    intro j hj
    by_cases hji : v j ≤ w i
    · have h:=WeightedPolynomial.IsWeighted.comp (hD j) (fun l=>hp.weighted l)
      exact (h.mono (Nat.sub_le_sub_right hji 1)).smul _
    · simp only [hR.coeff j i (Nat.lt_of_not_ge hji),zero_mul]
      exact WeightedPolynomial.IsWeighted.const w (w i-1) 0
  obtain ⟨P,hP,he⟩:=hsum
  exact ⟨P,hP,fun x=>(apply_eq_sum R _ i).trans (he x)⟩

end WeightedLinear
end
 
end

section
 

noncomputable section
namespace PolynomialShearPoint
open MvPolynomial FilteredShears.PolynomialShears
variable {σ : Type*}

def pointMap (A : MvPolynomial σ ℝ →ₐ[ℝ] MvPolynomial σ ℝ) (x : σ → ℝ) : σ → ℝ :=
  fun i=>eval x (A (X i))

lemma eval_pointMap (A : MvPolynomial σ ℝ →ₐ[ℝ] MvPolynomial σ ℝ)
    (x : σ → ℝ) (p : MvPolynomial σ ℝ) : eval (pointMap A x) p=eval x (A p) := by
  have he : aeval (pointMap A x)=(aeval x).comp A := by
    apply algHom_ext
    intro i
    simp [pointMap,aeval_eq_eval]
  exact DFunLike.congr_fun he p

lemma pointMap_comp (A B : MvPolynomial σ ℝ →ₐ[ℝ] MvPolynomial σ ℝ)
    (x : σ → ℝ) : pointMap A (pointMap B x)=pointMap (B.comp A) x := by
  funext i
  exact eval_pointMap B x (A (X i))

@[simp] lemma pointMap_id (x : σ → ℝ) : pointMap (AlgHom.id ℝ _) x=x := by
  funext i
  simp [pointMap]

def pointEquiv (A : MvPolynomial σ ℝ ≃ₐ[ℝ] MvPolynomial σ ℝ) : (σ → ℝ) ≃ (σ → ℝ) where
  toFun := pointMap A.toAlgHom
  invFun := pointMap A.symm.toAlgHom
  left_inv x := by rw [pointMap_comp]; simp
  right_inv x := by rw [pointMap_comp]; simp

 

theorem exists_shear (w : σ → ℕ) (hw : ∀ i,0 < w i)
    (D : (σ → ℝ) → (σ → ℝ))
    (hD : ∀ i,WeightedPolynomial.IsWeighted w (w i-1) (fun x=>D x i)) :
    ∃ A : shears (R:=ℝ) w,
      (∀ x,pointMap A.val.toAlgHom x=x+D x) ∧
      Function.Bijective (fun x=>x+D x) := by
  choose p hp he using hD
  have hp' (i : σ) : p i∈degreeLT w (w i) := by
    have h:= (WeightedPolynomial.bounded_iff_degreeLT (p i)).mp (hp i)
    rwa [Nat.sub_add_cancel (hw i)] at h
  let A:=ofDisplacements w p hp'
  have hA : A∈shears (R:=ℝ) w := by
    intro i
    simpa [A] using hp' i
  have ha (x : σ → ℝ) : pointMap A.toAlgHom x=x+D x := by
    funext i
    simp [pointMap,A,← he]
  refine ⟨⟨A,hA⟩,ha,?_⟩
  have hf : (fun x=>x+D x)=pointEquiv A := funext (fun x=>(ha x).symm)
  rw [hf]
  exact (pointEquiv A).bijective

end PolynomialShearPoint
end
 
end

section
 

noncomputable section
open MeasureTheory Filter Topology Set TopologicalSpace
namespace AsymptoticProbability
variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]

lemma levy_bound (μ ν : ProbabilityMeasure X) {ε : ℝ} (hε : 0≤ε)
    (h : ∀ A,MeasurableSet A → |(μ:Measure X).real A-(ν:Measure X).real A|≤ε) :
    levyProkhorovDist (μ:Measure X) (ν:Measure X) ≤ ε := by
  apply levyProkhorovDist_le_of_forall_le _ _ hε
  intro δ A hδ hA
  have hh : (μ:Measure X).real A ≤ (ν:Measure X).real A+δ := by
    have := (le_abs_self ((μ:Measure X).real A-(ν:Measure X).real A)).trans (h A hA)
    linarith
  have he : (μ:Measure X) A ≤ (ν:Measure X) A+ENNReal.ofReal δ := by
    apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) (by finiteness)).mp
    rw [ENNReal.toReal_add (measure_ne_top _ _) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (hε.trans hδ.le)]
    exact hh
  exact he.trans (add_le_add (measure_mono (Metric.self_subset_thickening (hε.trans_lt hδ) A)) le_rfl)

variable [SeparableSpace X]
lemma same_weak_limit {I : Type*} {l : Filter I} (μ ν : I → ProbabilityMeasure X)
    {ε : I → ℝ} (hε : Tendsto ε l (𝓝 0))
    (h : ∀ᶠ i in l,∀ A,MeasurableSet A →
      |(μ i:Measure X).real A-(ν i:Measure X).real A|≤ε i)
    {μ₀ : ProbabilityMeasure X} (ht : Tendsto μ l (𝓝 μ₀)) :
    Tendsto ν l (𝓝 μ₀) := by
  let e:=LevyProkhorov.probabilityMeasureHomeomorph (Ω:=X)
  have hb : Tendsto (fun i=>dist (e (μ i)) (e (ν i))) l (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _=>dist_nonneg)) _ hε
    filter_upwards [h] with i hi
    have hp:0≤ε i := by simpa using hi ∅ MeasurableSet.empty
    exact levy_bound (μ i) (ν i) hp hi
  have H: Tendsto (fun i=>e (ν i)) l (𝓝 (e μ₀)) :=
    (e.continuous.continuousAt.tendsto.comp ht).congr_dist hb
  simpa only [Function.comp_def,Homeomorph.symm_apply_apply] using e.symm.continuous.continuousAt.tendsto.comp H

omit [PseudoMetricSpace X] [BorelSpace X] [SeparableSpace X] in
lemma pushed_event_bound {Y : Type*} [MeasurableSpace Y]
    (μ : ProbabilityMeasure Y) (q : Y → X) (hq : Measurable q)
    (T : Y → Y) (hT : Measurable T) (V : X → X) (hV : Measurable V)
    (he : ∀ y,q (T y)=V (q y)) {ε : ℝ}
    (h : ∀ B,MeasurableSet B →
      |(μ.map T : Measure Y).real B-(μ:Measure Y).real B|≤ε) :
    ∀ A,MeasurableSet A →
      |((μ.map q).map V : Measure X).real A-
        (μ.map q : Measure X).real A|≤ε := by
  intro A hA
  have H:=h (q ⁻¹' A) (hA.preimage hq)
  change |(Measure.map V (Measure.map q (μ:Measure Y))).real A-
    (Measure.map q (μ:Measure Y)).real A|≤ε
  change |(Measure.map T (μ:Measure Y)).real (q ⁻¹' A)-(μ:Measure Y).real (q ⁻¹' A)|≤ε at H
  rw [map_measureReal_apply hT (hA.preimage hq)] at H
  rw [map_measureReal_apply hV hA,map_measureReal_apply hq (hA.preimage hV),
    map_measureReal_apply hq hA]
  have hh : T ⁻¹' (q ⁻¹' A)=q ⁻¹' (V ⁻¹' A) := by
    ext y
    exact Iff.of_eq (congrArg (·∈A) (he y))
  rwa [hh] at H

variable {G : Type*} [Group G] [MulAction G X] [ContinuousConstSMul G X]

lemma cluster_invariant {I : Type*} {l : Filter I} (μ : I → ProbabilityMeasure X)
    (h : ∀ g : G,∃ ε : I → ℝ,Tendsto ε l (𝓝 0) ∧
      ∀ᶠ i in l,∀ A,MeasurableSet A →
        |((μ i).map (g • ·) : Measure X).real A-
          (μ i:Measure X).real A|≤ε i)
    {ν : ProbabilityMeasure X} (hc : MapClusterPt ν l μ) :
    SMulInvariantMeasure G X (ν:Measure X) := by
  obtain ⟨U,hUl,hU⟩:=mapClusterPt_iff_ultrafilter.mp hc
  have he (g : G) : ν.map (g • ·)=ν := by
    obtain ⟨ε,hε,hεb⟩:=h g
    have hεb' : ∀ᶠ i in (U:Filter I),∀ A,MeasurableSet A →
        |(μ i:Measure X).real A-
          ((μ i).map (g • ·) : Measure X).real A|≤ε i := by
      filter_upwards [hUl hεb] with i hi A hA
      rw [abs_sub_comm]
      exact hi A hA
    have ht:=same_weak_limit μ (fun i=>(μ i).map (g • ·))
      (hε.mono_left hUl) hεb' hU
    have hmap:=ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous μ ν hU
      (continuous_const_smul g)
    exact tendsto_nhds_unique hmap ht
  refine ⟨?_⟩
  intro g A hA
  have hh : Measure.map (g • ·) (ν:Measure X)=(ν:Measure X) :=
    congrArg (fun z : ProbabilityMeasure X=>(z:Measure X)) (he g)
  rw [← Measure.map_apply (measurable_const_smul g) hA,hh]

lemma weak_haar_of_unique [CompactSpace X] [T2Space X]
    {I : Type*} {l : Filter I} (μ : I → ProbabilityMeasure X)
    (ν : ProbabilityMeasure X)
    (huniq : ∀ θ : ProbabilityMeasure X,SMulInvariantMeasure G X (θ:Measure X) → θ=ν)
    (h : ∀ g : G,∃ ε : I → ℝ,Tendsto ε l (𝓝 0) ∧
      ∀ᶠ i in l,∀ A,MeasurableSet A →
        |((μ i).map (g • ·) : Measure X).real A-
          (μ i:Measure X).real A|≤ε i) :
    Tendsto μ l (𝓝 ν) := by
  apply tendsto_nhds_of_unique_mapClusterPt
  intro θ hθ
  exact huniq θ (cluster_invariant μ h hθ)

end AsymptoticProbability

end
end
end

end OAI
