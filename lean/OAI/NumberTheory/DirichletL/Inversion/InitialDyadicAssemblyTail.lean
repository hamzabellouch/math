import OAI.NumberTheory.DirichletL.Inversion.InitialDyadicAssemblyRetained

namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialDyadicAssembly
local notation "Eis"=>ActualEisensteinCubic.O
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerWindows InverseInitialProfile InverseInitialClippedColumns
open CenteredMomentSectorLocalization CenteredMomentDyadicCount

def windowMass {a b:Fin 4→ℝ}(F:Finset (Windows a b))(q:Fin 4→ℝ) : ℝ :=
  ∑k∈F,∏i:Fin 4,dyadicWeight (k i).val (q i)

theorem windowMass_cast {a b:Fin 4→ℝ}(F:Finset (Windows a b))(q:Fin 4→ℝ) :
    (windowMass F q:ℂ)=∑k∈F,weight (fun i=>(k i).val) q := by
  simp only [windowMass,weight,Complex.ofReal_sum,Complex.ofReal_prod]

theorem windowMass_nonneg {a b:Fin 4→ℝ}(F:Finset (Windows a b))(q:Fin 4→ℝ) :
    0≤windowMass F q := by
  apply Finset.sum_nonneg
  intro k hk
  exact Finset.prod_nonneg (fun i hi=>(dyadicWeight_bounds (k i).val (q i)).1)

theorem windowMass_univ (a b q:Fin 4→ℝ)(ha:∀i,0<a i)
    (hq:∀i,q i∈Set.Icc (a i) (b i)) :
    windowMass (Finset.univ:Finset (Windows a b)) q=1 := by
  apply Complex.ofReal_injective
  rw [windowMass_cast,Complex.ofReal_one]
  exact weight_partition a b q ha hq

theorem windowMass_le_one {a b:Fin 4→ℝ}(F:Finset (Windows a b))(q:Fin 4→ℝ)
    (ha:∀i,0<a i)(hq:∀i,q i∈Set.Icc (a i) (b i)) : windowMass F q≤1 := by
  rw [←windowMass_univ a b q ha hq]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ F)
    (fun k hk hnot=>Finset.prod_nonneg (fun i hi=>(dyadicWeight_bounds (k i).val (q i)).1))

theorem windowMass_norm_le_one {a b:Fin 4→ℝ}(F:Finset (Windows a b))(q:Fin 4→ℝ)
    (ha:∀i,0<a i)(hq:∀i,q i∈Set.Icc (a i) (b i)) : ‖(windowMass F q:ℂ)‖≤1 := by
  simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (windowMass_nonneg F q)]
    using windowMass_le_one F q ha hq

theorem windowMass_ne_zero_exists {a b:Fin 4→ℝ}(F:Finset (Windows a b))(q:Fin 4→ℝ)
    (h:windowMass F q≠0) : ∃k∈F,weight (fun i=>(k i).val) q≠0 := by
  have hc:(windowMass F q:ℂ)≠0:=by exact_mod_cast h
  rw [windowMass_cast] at hc
  exact Finset.exists_ne_zero_of_sum_ne_zero hc

variable {ι:Type*}[DecidableEq ι](p:ι→Eis)
  (hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem windowBlock_eq_full
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(hZ:1<Z)(k:Fin 4→ℤ) :
    windowBlock p hp hcop hg pool S w Ψ j marks W₁ W₂ Φ Z D m k =
      physicalBlock p hp hcop hg (pointSource pool S)
        ((fun x=>w x*weight k (sourceNorms p x))∘erasePoint) Ψ j marks W₁ W₂ Φ Z D m := by
  simp_rw [source_weight_cutoff p Z D hZ]
  exact (physicalBlock_windowSource p hp hcop hg pool S cutoff Z D _ _ _ _ m
    w Ψ j marks W₁ W₂ Φ).symm

theorem sum_windowBlock_eq_mass
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (a b:Fin 4→ℝ)(F:Finset (Windows a b))
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(hZ:1<Z) :
    (∑k∈F,windowBlock p hp hcop hg pool S w Ψ j marks W₁ W₂ Φ Z D m (fun i=>(k i).val)) =
      physicalBlock p hp hcop hg (pointSource pool S)
        ((fun x=>w x*(windowMass F (sourceNorms p x):ℂ))∘erasePoint)
        Ψ j marks W₁ W₂ Φ Z D m := by
  simp_rw [windowBlock_eq_full p hp hcop hg pool S w Ψ j marks W₁ W₂ Φ Z D m hZ]
  unfold physicalBlock
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ρ hρ
  simp only [Function.comp_apply]
  rw [←Finset.sum_mul,←Finset.mul_sum,←windowMass_cast]

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem mass_weight_bound
    (a b:Fin 4→ℝ)(F:Finset (Windows a b))(ha:∀i,0<a i)
    (w:Source (ι:=ι) 0→ℂ)(x:Source (ι:=ι) 0)
    (hx:∀i,sourceNorms p x i∈Set.Icc (a i) (b i)) :
    ‖w x*(windowMass F (sourceNorms p x):ℂ)‖≤‖w x‖ := by
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (windowMass_norm_le_one F _ ha hx)

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem tail_mass_live (a b:Fin 4→ℝ)(Z D m L:ℝ)(hZ:1<Z)
    (x:Source (ι:=ι) 0)
    (hn:windowMass (tailWindows a b Z D m L) (sourceNorms p x)≠0) :
    ∃k∈tailWindows a b Z D m L,
      L<radialCenter m (exponent Z (k 3).val) (exponent Z (k 1).val) D (exponent Z (k 0).val) ∧
      outerCutoff cutoff (sourceRelative p x Z D (exponent Z (k 0).val)
        (exponent Z (k 2).val) (exponent Z (k 1).val) (exponent Z (k 3).val))≠0 := by
  obtain ⟨k,hk,hne⟩:=windowMass_ne_zero_exists _ _ hn
  refine ⟨k,hk,(Finset.mem_filter.mp hk).2,?_⟩
  rwa [source_weight_cutoff p Z D hZ] at hne

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem tail_mass_live_bounds (a b:Fin 4→ℝ)(Z D m L:ℝ)(hZ:1<Z)
    (x:Source (ι:=ι) 0)
    (hn:windowMass (tailWindows a b Z D m L) (sourceNorms p x)≠0) :
    ∃k∈tailWindows a b Z D m L,
      L<radialCenter m (exponent Z (k 3).val) (exponent Z (k 1).val) D (exponent Z (k 0).val) ∧
      ∀i,sourceNorms p x i∈Set.Ioo (Z^(exponent Z (k i).val)/4) (Z^(exponent Z (k i).val)) := by
  obtain ⟨k,hk,hne⟩:=windowMass_ne_zero_exists _ _ hn
  refine ⟨k,hk,(Finset.mem_filter.mp hk).2,?_⟩
  intro i
  have hi:(dyadicWeight (k i).val (sourceNorms p x i):ℂ)≠0 :=
    Finset.prod_ne_zero_iff.mp hne i (Finset.mem_univ i)
  have hr:dyadicWeight (k i).val (sourceNorms p x i)≠0 := by exact_mod_cast hi
  rw [exponent_scale Z hZ]
  exact dyadicWeight_support (k i).val hr

theorem physicalBlock_filter_of_live
    (source:Finset (Point ι))(P:Point ι→Prop)(w:Point ι→ℂ)
    (Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)
    (hP:∀x∈source,∀ρ:SecondRayIndex,
      w x*physicalTerm p hp hcop hg Ψ j marks W₁ W₂ Φ Z D m x ρ≠0→P x) :
    physicalBlock p hp hcop hg source w Ψ j marks W₁ W₂ Φ Z D m =
      physicalBlock p hp hcop hg (source.filter P) w Ψ j marks W₁ W₂ Φ Z D m := by
  unfold physicalBlock
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hh:P x
  · rw [ite_eq_left hh]
  · rw [ite_eq_right hh]
    apply Finset.sum_eq_zero
    intro ρ hρ
    by_contra hn
    exact hh (hP x hx ρ hn)

theorem physicalBlock_mass_filter
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (a b:Fin 4→ℝ)(F:Finset (Windows a b))
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ) :
    physicalBlock p hp hcop hg (pointSource pool S)
      ((fun x=>w x*(windowMass F (sourceNorms p x):ℂ))∘erasePoint)
      Ψ j marks W₁ W₂ Φ Z D m =
    physicalBlock p hp hcop hg
      (pointSource pool (S.filter (fun x=>windowMass F (sourceNorms p x)≠0)))
      ((fun x=>w x*(windowMass F (sourceNorms p x):ℂ))∘erasePoint)
      Ψ j marks W₁ W₂ Φ Z D m := by
  unfold physicalBlock
  rw [pointSource_sum,pointSource_sum,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hn:windowMass F (sourceNorms p x)=0
  · simp only [hn,ne_eq,not_true_eq_false,ite_false,Function.comp_apply,
      erase_sourcePoint,Complex.ofReal_zero,mul_zero,zero_mul,Finset.sum_const_zero]
  · rw [ite_eq_left hn]

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem exists_source_frequency_cap (S:Finset (Source (ι:=ι) 0)) :
    ∃T:ℝ,0<T ∧ ∀x∈S,sourceNorms p x 3≤T := by
  have hn (x:Source (ι:=ι) 0) : 0≤sourceNorms p x 3 := by
    change 0≤‖ConcreteTraceCRT.eisEmbedding x.frequency‖^2
    positivity
  have hs:0≤∑x∈S,sourceNorms p x 3:=Finset.sum_nonneg (fun x hx=>hn x)
  refine ⟨1+∑x∈S,sourceNorms p x 3,by linarith,?_⟩
  intro x hx
  have he:sourceNorms p x 3≤∑y∈S,sourceNorms p y 3 :=
    Finset.single_le_sum (fun y hy=>hn y) hx
  linarith

theorem actual_physical_retained_tail
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (hdiv:∀x∈S,x.divisor⊆x.common)(hf:∀x∈S,x.frequency≠0)
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m b T L:ℝ)(hZ:1<Z)
    (hW₁:Function.support W₁⊆Set.Iic b)(hW₂:Function.support W₂⊆Set.Iic b)
    (hT:∀x∈S,sourceNorms p x 3≤T) :
    physicalBlock p hp hcop hg (pointSource pool S) (w∘erasePoint) Ψ j marks W₁ W₂ Φ Z D m =
    (∑k∈retainedWindows (fun _=>1) (physicalCaps b Z D T) Z D m L,
      windowBlock p hp hcop hg pool (cappedSource p S (fun _=>1) (physicalCaps b Z D T))
        w Ψ j marks W₁ W₂ Φ Z D m (fun i=>(k i).val)) +
    physicalBlock p hp hcop hg
      (pointSource pool (cappedSource p S (fun _=>1) (physicalCaps b Z D T)))
      ((fun x=>w x*(windowMass (tailWindows (fun _=>1) (physicalCaps b Z D T) Z D m L)
        (sourceNorms p x):ℂ))∘erasePoint) Ψ j marks W₁ W₂ Φ Z D m := by
  rw [actual_physical_partition p hp hcop hg hpr pool S hdiv hf w Ψ j marks W₁ W₂ Φ
    Z D m b T hZ hW₁ hW₂ hT]
  rw [window_sum_split (fun _=>1) (physicalCaps b Z D T) Z D m L]
  congr 1
  exact sum_windowBlock_eq_mass p hp hcop hg pool
    (cappedSource p S (fun _=>1) (physicalCaps b Z D T)) _ _ _ w Ψ j marks W₁ W₂ Φ Z D m hZ

end SevenEighths.InverseInitialDyadicAssembly

end

end OAI
