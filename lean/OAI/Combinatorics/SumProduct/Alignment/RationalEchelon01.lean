import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.WordPlan03
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
section
section
 

 

noncomputable section
open MeasureTheory Filter Topology
open scoped NNReal ENNReal
namespace AllLevelFactorization.Factorization
open RationalLattice CubeFaces ResidueCover
open ConstructedWordPlan.GlobalWordPlan
open ConstructedWordPlan.AlignmentScales ConstructedWordPlan.RationalPivotPlan
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {k s : ℕ} {c : RealCoordinates G k} {Γ : Subgroup G}
variable {K : Filtration G} {P : ℕ → ℤ → G} {L : ℕ → ℝ}
variable (E : Factorization c Γ s K P L)
variable (C : (r : Fin E.period) → E.ResidueCover r)
variable [∀ r,MeasurableSpace ((C r).CubeSpace (ι:=Empty))]
variable [∀ r,BorelSpace ((C r).CubeSpace (ι:=Empty))]
variable [MeasurableSpace (G⧸Γ)] [BorelSpace (G⧸Γ)]
variable [CompactSpace (G⧸Γ)] [SecondCountableTopology (G⧸Γ)]
variable [HasOuterApproxClosed (G⧸Γ)] [MeasurableSingletonClass (G⧸Γ)]
variable {n r : ℕ} (hs : 1 ≤ s) (D : Pivot n)
variable (F B : Finset (Scale n))
variable (q₀ : ℕ) (hq₀ : pivotModulus s r hs D F B∣q₀)
variable (b : Scale n) (hb : b∈B) {τ : ℝ} (hτ : 0<τ)
variable (Y : Fin D.targets → Type) [∀ j,TopologicalSpace (Y j)]
variable [∀ j,MulAction (Shifts D) (Y j)]
variable (π : (j : Fin D.targets) → (G⧸Γ) → Y j)
variable (Read : (j : Fin D.targets) → ℚ → Y j × Slots D → Fin r → ℝ)
variable (hπ : ∀ j,Continuous (π j))
variable (hRead : ∀ j a t,Continuous (fun y=>Read j a y t))
variable (hS : ∀ j (a : Shifts D),Continuous (fun y : Y j=>a • y))
variable (M : ∀ a : Fin E.period,∀ β : ℝ,
  PhysicalMarginalFaceData D (C a).pivotChart.chart (C a).pointFiltration (C a).pointLattice
    π ((C a).pivotImage β) s)

include hπ hRead hS M hq₀ hb hτ in
 

theorem physical_pivot_empirical_success_mass (hL : ∀ N,0<L N) (ht : Tendsto L atTop atTop)
    (ReadN : ℕ → (j : Fin D.targets) → ℚ → Y j × Slots D → Fin r → ℝ)
    (he : ∀ᶠ N in atTop,∀ p∈pivotOptions s r hs D F,∀ i x,
      |centerReading D Y π (ReadN N) F q₀ b p i x-centerReading D Y π Read F q₀ b p i x| ≤ τ/4 ∧
      |translatedReading D Y π (ReadN N) F q₀ b p i x-translatedReading D Y π Read F q₀ b p i x| ≤ τ/4) :
    ∀ᶠ N in atTop,(((((pivotOptions s r hs D F).card : ℝ≥0)⁻¹/2) : ℝ≥0) : ℝ≥0∞) <
      (E.empiricalPointLaw N : Measure (G⧸Γ))
        (⋃ p∈pivotOptions s r hs D F,AlignmentMass.Success τ
          (centerReading D Y π (ReadN N) F q₀ b p)
          (translatedReading D Y π (ReadN N) F q₀ b p)) := by
  classical
  let O:=↥(pivotOptions s r hs D F)
  let : Nonempty O:=⟨⟨(pivotOptions_nonempty s r hs D F).choose,
    (pivotOptions_nonempty s r hs D F).choose_spec⟩⟩
  let A (p : O):=centerReading D Y π Read F q₀ b p.val
  let T (p : O):=translatedReading D Y π Read F q₀ b p.val
  let AN (N : ℕ) (p : O):=centerReading D Y π (ReadN N) F q₀ b p.val
  let TN (N : ℕ) (p : O):=translatedReading D Y π (ReadN N) F q₀ b p.val
  have hq : 0<((pivotOptions s r hs D F).card : ℝ≥0) := by
    exact_mod_cast Finset.card_pos.mpr (pivotOptions_nonempty s r hs D F)
  have hhalf : (((((pivotOptions s r hs D F).card : ℝ≥0)⁻¹/2) : ℝ≥0) : ℝ≥0∞) <
      (((pivotOptions s r hs D F).card : ℝ≥0)⁻¹ : ℝ≥0∞) :=
    by simpa only [ENNReal.coe_inv (ne_of_gt hq)] using
      (ENNReal.coe_lt_coe.mpr (half_lt_self (inv_pos.mpr hq)))
  have hm:=E.physical_pivot_mixture_mass C hs D F B q₀ hq₀ b hb τ Y π Read hπ hRead hS M
  have hm' : (((pivotOptions s r hs D F).card : ℝ≥0)⁻¹ : ℝ≥0∞) ≤
      (E.pointMixture C : Measure (G⧸Γ)) (⋃ p : O,AlignmentMass.ClosedGood τ (A p) (T p)) := by
    simpa only [O,A,T,Set.iUnion_subtype,closedOption] using hm
  have he' : ∀ᶠ N in atTop,∀ (p : O) i x,
      |AN N p i x-A p i x| ≤ τ/4 ∧ |TN N p i x-T p i x| ≤ τ/4 := by
    filter_upwards [he] with N hN p i x
    exact hN p.val p.property i x
  have hh:=AlignmentMass.eventually_success_mass (E.pointMixture C) E.empiricalPointLaw
    (E.weak_point_law C hL ht) hτ A T AN TN
    (fun p=>centerReading_continuous D π Read hπ hRead F q₀ b p.val)
    (fun p=>translatedReading_continuous D π Read hπ hRead hS F q₀ b p.val)
    he' hhalf hm'
  simpa only [O,AN,TN,Set.iUnion_subtype] using hh

end AllLevelFactorization.Factorization
end
 
end

section
 

 

noncomputable section
namespace CubeFaces
variable {G H ι : Type*} [Group G] [Group H] [DecidableEq ι]
variable (p : G →* H)

def vertexMap : (Finset ι → G) →* (Finset ι → H) where
  toFun f w:=p (f w)
  map_one' := by ext w; exact p.map_one
  map_mul' f g:=by ext w; exact p.map_mul _ _

omit [DecidableEq ι] in
@[simp] lemma vertexMap_apply (f : Finset ι → G) (w : Finset ι) :
    vertexMap p f w=p (f w) := rfl

lemma vertexMap_face (D : Finset ι) :
    (vertexMap p).comp (face D)=(face D).comp p := by
  ext g w
  simp only [MonoidHom.comp_apply,vertexMap_apply,face_apply]
  split_ifs <;> simp

lemma map_cube (K : Filtration G) (L : Filtration H)
    (honto : ∀ j,(K.level j).map p=L.level j) (I : Finset ι) (l : ℕ) :
    (cube K I l).map (vertexMap p)=cube L I l := by
  simp only [cube,Subgroup.map_iSup,Subgroup.map_map,vertexMap_face]
  simp only [←Subgroup.map_map,honto]

lemma exists_cube_lift (K : Filtration G) (L : Filtration H)
    (honto : ∀ j,(K.level j).map p=L.level j) (I : Finset ι) (l : ℕ)
    (f : Finset ι → H) (hf : f∈cube L I l) :
    ∃ g∈cube K I l,∀ w,p (g w)=f w := by
  rw [←map_cube p K L honto I l] at hf
  obtain ⟨g,hg,he⟩:=hf
  exact ⟨g,hg,fun w=>congrFun he w⟩

end CubeFaces
end
 
end

section
 

 

noncomputable section
open scoped BigOperators
namespace RationalEchelon

variable {K : Type*} [Field K]

structure Chart {n : ℕ} (W : Submodule K (Fin n → K)) where
  dim : ℕ
  pivot : Fin dim → Fin n
  mono : StrictMono pivot
  embed : (Fin dim → K) →ₗ[K] (Fin n → K)
  mem : ∀ x,embed x∈W
  onto : ∀ v∈W,∃ x,embed x=v
  at_pivot : ∀ x i,embed x (pivot i)=x i
  prefix_eq : ∀ j x y,(∀ i,pivot i ≤ j → x i=y i) → embed x j=embed y j

def dropLast (n : ℕ) : (Fin (n+1) → K) →ₗ[K] (Fin n → K) where
  toFun x i:=x i.castSucc
  map_add' _ _:=rfl
  map_smul' _ _:=rfl

def snocZero (n : ℕ) : (Fin n → K) →ₗ[K] (Fin (n+1) → K) where
  toFun x:=Fin.snoc x 0
  map_add' x y:=by ext i; refine Fin.lastCases ?_ (fun i=>?_) i <;> simp
  map_smul' a x:=by ext i; refine Fin.lastCases ?_ (fun i=>?_) i <;> simp

lemma expansion {n : ℕ} (x : Fin n → K) : x=∑ i : Fin n,x i • Pi.single i 1 := by
  ext j
  simp [Finset.sum_apply,Pi.smul_apply,Pi.single_apply]

 

lemma lift {n d : ℕ} (W : Submodule K (Fin (n+1) → K))
    (e : (Fin d → K) →ₗ[K] (Fin n → K))
    (he : ∀ x,e x∈W.map (dropLast n)) :
    ∃ f : (Fin d → K) →ₗ[K] (Fin (n+1) → K),
      (∀ x,f x∈W) ∧ ∀ x,dropLast n (f x)=e x := by
  have hex (i : Fin d) : ∃ b∈W,dropLast n b=e (Pi.single i 1) :=
    Submodule.mem_map.mp (he _)
  choose b hb hpb using hex
  let f : (Fin d → K) →ₗ[K] (Fin (n+1) → K):=
    ∑ i : Fin d,(LinearMap.proj i).smulRight (b i)
  have hf (x) : f x=∑ i : Fin d,x i • b i := by simp [f,LinearMap.sum_apply]
  refine ⟨f,?_,?_⟩
  · intro x
    rw [hf]
    exact W.sum_mem (fun i _=>W.smul_mem _ (hb i))
  · intro x
    rw [hf,map_sum]
    simp only [map_smul,hpb]
    conv_rhs=>rw [expansion x,map_sum]
    simp

 

theorem chart_exists {n : ℕ} (W : Submodule K (Fin n → K)) : Nonempty (Chart W) := by
  induction n with
  | zero =>
    exact ⟨{ dim:=0
             pivot:=Fin.elim0
             mono:=by intro i; exact Fin.elim0 i
             embed:=0
             mem:=by intro x; exact W.zero_mem
             onto:=by intro v hv; exact ⟨Fin.elim0,Subsingleton.elim _ _⟩
             at_pivot:=by intro x i; exact Fin.elim0 i
             prefix_eq:=by intro j; exact Fin.elim0 j }⟩
  | succ n ih =>
    let V:=W.map (dropLast n)
    obtain ⟨E⟩:=ih V
    obtain ⟨f,hf,hpf⟩:=lift W E.embed E.mem
    by_cases hker : ∀ v∈W,dropLast n v=0 → v=0
    · have hinj : ∀ u∈W,∀ v∈W,dropLast n u=dropLast n v → u=v := by
        intro u hu v hv huv
        apply sub_eq_zero.mp
        apply hker (u-v) (W.sub_mem hu hv)
        rw [map_sub,huv,sub_self]
      refine ⟨{ dim:=E.dim
                pivot:=fun i=>(E.pivot i).castSucc
                mono:=by intro i j hij; exact E.mono hij
                embed:=f
                mem:=hf
                onto:=?_
                at_pivot:=?_
                prefix_eq:=?_ }⟩
      · intro v hv
        obtain ⟨x,hx⟩:=E.onto (dropLast n v) (Submodule.mem_map.mpr ⟨v,hv,rfl⟩)
        exact ⟨x,hinj _ (hf _) _ hv ((hpf x).trans hx)⟩
      · intro x i
        exact (congrFun (hpf x) (E.pivot i)).trans (E.at_pivot x i)
      · intro j x y hxy
        revert hxy
        refine Fin.lastCases ?_ (fun j=>?_) j <;> intro hxy
        · have he : x=y:=funext fun i=>hxy i (Fin.le_last _)
          rw [he]
        · exact (congrFun (hpf x) j).trans ((E.prefix_eq j x y (fun i hi=>hxy i hi)).trans
            (congrFun (hpf y) j).symm)
    · push Not at hker
      obtain ⟨v,hv,hpv,hv0⟩:=hker
      have hvl : v (Fin.last n)≠0 := by
        intro hh
        apply hv0
        ext i
        refine Fin.lastCases hh (fun i=>?_) i
        exact congrFun hpv i
      have haxis : Pi.single (Fin.last n) (1:K)∈W := by
        have he : (v (Fin.last n))⁻¹ • v=Pi.single (Fin.last n) 1 := by
          ext i
          refine Fin.lastCases ?_ (fun i=>?_) i
          · simp [hvl]
          · have hz : v i.castSucc=0:=congrFun hpv i
            simp [hz,Fin.castSucc_ne_last]
        rw [← he]
        exact W.smul_mem _ hv
      have hzero (x : Fin E.dim → K) : snocZero n (E.embed x)∈W := by
        have hx:=hf x
        have he : snocZero n (E.embed x)=f x-f x (Fin.last n) • Pi.single (Fin.last n) 1 := by
          ext i
          refine Fin.lastCases ?_ (fun i=>?_) i
          · simp [snocZero]
          · have hh:=congrFun (hpf x) i
            simpa [snocZero,dropLast,Fin.castSucc_ne_last] using hh.symm
        rw [he]
        exact W.sub_mem hx (W.smul_mem _ haxis)
      let e : (Fin (E.dim+1) → K) →ₗ[K] (Fin (n+1) → K) :=
        (snocZero n).comp (E.embed.comp (dropLast E.dim)) +
          (LinearMap.proj (Fin.last E.dim)).smulRight (Pi.single (Fin.last n) 1)
      have he (x : Fin (E.dim+1) → K) : e x=Fin.snoc (E.embed (dropLast E.dim x)) (x (Fin.last E.dim)) := by
        ext i
        refine Fin.lastCases ?_ (fun i=>?_) i <;>
          simp [e,snocZero,Fin.castSucc_ne_last]
      let p : Fin (E.dim+1) → Fin (n+1):=Fin.snoc (fun i=>(E.pivot i).castSucc) (Fin.last n)
      refine ⟨{ dim:=E.dim+1
                pivot:=p
                mono:=?_
                embed:=e
                mem:=?_
                onto:=?_
                at_pivot:=?_
                prefix_eq:=?_ }⟩
      · intro i j hij
        revert hij
        refine Fin.lastCases ?_ (fun j=>?_) j <;> intro hij
        · have hi : i≠Fin.last E.dim:=ne_of_lt hij
          obtain ⟨i,rfl⟩:=Fin.eq_castSucc_of_ne_last hi
          simp [p]
        · revert hij
          refine Fin.lastCases ?_ (fun i=>?_) i <;> intro hij
          · exact False.elim (not_lt_of_ge (Fin.le_last _) hij)
          · simpa [p] using E.mono hij
      · intro x
        exact W.add_mem (hzero _) (W.smul_mem _ haxis)
      · intro y hy
        obtain ⟨x,hx⟩:=E.onto (dropLast n y) (Submodule.mem_map.mpr ⟨y,hy,rfl⟩)
        refine ⟨Fin.snoc x (y (Fin.last n)),?_⟩
        rw [he]
        have hd : dropLast E.dim (Fin.snoc x (y (Fin.last n)))=x:=by ext i; simp [dropLast]
        rw [hd,hx]
        ext i
        refine Fin.lastCases ?_ (fun i=>?_) i <;> simp [dropLast]
      · intro x i
        refine Fin.lastCases ?_ (fun i=>?_) i
        · simp [he,p]
        · simpa [he,p,dropLast] using E.at_pivot (dropLast E.dim x) i
      · intro j x y hxy
        revert hxy
        refine Fin.lastCases ?_ (fun j=>?_) j <;> intro hxy
        · simp only [he,Fin.snoc_last]
          exact hxy (Fin.last E.dim) (by simp [p])
        · simp only [he,Fin.snoc_castSucc]
          apply E.prefix_eq
          intro i hi
          exact hxy i.castSucc (by simpa [p] using hi)

end RationalEchelon

end
end
end

end OAI
