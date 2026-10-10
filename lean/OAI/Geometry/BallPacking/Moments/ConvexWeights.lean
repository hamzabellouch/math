import Mathlib
import OAI.Geometry.BallPacking.Moments.AnalyticBoundary
import OAI.Geometry.BallPacking.Forms.ManifoldExteriorAlgebra

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.FiniteMoment
open scoped BigOperators
open Set
section
variable {ι E : Type*} [Fintype ι] [AddCommGroup E] [Module ℝ E]

 theorem convexHull_range_weights {w : ι → E} {p : E}
    (hp : p∈convexHull ℝ (range w)) :
    ∃ h : ι → ℝ,(∀ i,0≤h i) ∧ (∑ i,h i)=1 ∧ ∑ i,h i • w i=p := by
  classical
  rw [convexHull_range_eq_exists_affineCombination] at hp
  obtain ⟨s,c,hc,hs,hp⟩ := hp
  refine ⟨fun i => if i∈s then c i else 0,?_,?_,?_⟩
  · intro i
    dsimp only
    split_ifs with hi
    · exact hc i hi
    · exact le_rfl
  · simpa only [Finset.sum_ite_mem,Finset.univ_inter] using hs
  · rw [Finset.affineCombination_eq_linear_combination _ _ _ hs] at hp
    simpa only [ite_smul,zero_smul,Finset.sum_ite_mem,Finset.univ_inter] using hp

end

 def closedTrapezoid (A B : ℝ) : Set MomentPlane :=
  {p | 0≤p 0 ∧ p 0≤A ∧ 0≤p 1 ∧ p 0+p 1≤B}

 theorem closedTrapezoid_mem_convexHull {A B : ℝ} (hA : 0<A) (hAB : A≤B)
    {p : MomentPlane} (hp : p∈closedTrapezoid A B) :
    p∈convexHull ℝ (range (trapezoidCorners A B)) := by
  by_cases hz : B-p 0=0
  · have hp0 : p 0=A := by linarith [hp.2.1]
    have hp1 : p 1=0 := by linarith [hp.2.2.1,hp.2.2.2]
    have he : p=trapezoidCorners A B 1 := by
      ext j
      fin_cases j <;> simp [trapezoidCorners,planeVector,hp0,hp1]
    exact he ▸ subset_convexHull ℝ _ (mem_range_self 1)
  have hB : 0<B-p 0 := lt_of_le_of_ne (by linarith [hp.2.2.1,hp.2.2.2]) (Ne.symm hz)
  let l := p 0/A
  let t := p 1/(B-p 0)
  have hl0 : 0≤l := div_nonneg hp.1 hA.le
  have hl1 : l≤1 := (div_le_one hA).mpr hp.2.1
  have ht0 : 0≤t := div_nonneg hp.2.2.1 hB.le
  have ht1 : t≤1 := (div_le_one hB).mpr (by linarith [hp.2.2.2])
  let c : Fin 4 → ℝ := ![(1-l)*(1-t),l*(1-t),l*t,(1-l)*t]
  apply mem_convexHull_of_exists_fintype c (trapezoidCorners A B)
  · intro i
    fin_cases i <;> dsimp [c] <;> positivity
  · simp only [c,Fin.sum_univ_succ]
    dsimp
    ring
  · intro i
    exact mem_range_self i
  · ext j
    fin_cases j <;>
      simp [c,trapezoidCorners,planeVector,Fin.sum_univ_succ,l,t] <;>
      field_simp <;> ring

 theorem convex_affine_height_preimage {H : Set (MomentPlane × ℝ)}
    (hH : Convex ℝ H) (S : ℝ) : Convex ℝ {p : MomentPlane | (p,S-p 0-p 1)∈H} := by
  intro p hp q hq a b ha hb hab
  have he := hH hp hq ha hb hab
  change (a • p + b • q,S-(a • p+b • q) 0-(a • p+b • q) 1)∈H
  convert he using 2
  change S-(a*p 0+b*q 0)-(a*p 1+b*q 1)=a*(S-p 0-p 1)+b*(S-q 0-q 1)
  linear_combination -S * hab

 theorem convex_zero_height_preimage {H : Set (MomentPlane × ℝ)}
    (hH : Convex ℝ H) : Convex ℝ {p : MomentPlane | (p,0)∈H} := by
  intro p hp q hq a b ha hb hab
  change (a • p+b • q,0)∈H
  simpa only [Prod.smul_mk,Prod.mk_add_mk,smul_zero,add_zero] using hH hp hq ha hb hab

 def markedHeight (S : ℝ) (p : MomentPlane) : ℝ := max (S-p 0-p 1) 0
 def heightGraph (A B S : ℕ) (k : TrapezoidWeight A B) : MomentPlane × ℝ :=
  (trapezoidWeight A B k,markedHeight S (trapezoidWeight A B k))
 def heightHull (A B S : ℕ) : Set (MomentPlane × ℝ) := convexHull ℝ (range (heightGraph A B S))

 def latticeIndex {A B i j : ℕ} (hi : i ≤ A) (hij : i+j ≤ B) : TrapezoidWeight A B :=
  ⟨(⟨i,by omega⟩,⟨j,by omega⟩),hi,hij⟩

 theorem lattice_height_mem {A B S i j : ℕ} (hi : i ≤ A) (hij : i+j ≤ B) :
    (planeVector i j,markedHeight S (planeVector i j))∈heightHull A B S :=
  subset_convexHull ℝ _ ⟨latticeIndex hi hij,rfl⟩

 theorem lattice_lower_mem {A B S i j : ℕ} (hi : i ≤ A) (hij : i+j ≤ B) (hs : i+j ≤ S) :
    (planeVector i j,(S:ℝ)-i-j)∈heightHull A B S := by
  have hs' : (i:ℝ)+j ≤ S := by exact_mod_cast hs
  have he := lattice_height_mem (S := S) hi hij
  change (planeVector i j,max ((S:ℝ)-i-j) 0)∈heightHull A B S at he
  simpa only [max_eq_left (by linarith : 0 ≤ (S:ℝ)-i-j)] using he

 theorem lattice_upper_mem {A B S i j : ℕ} (hi : i ≤ A) (hij : i+j ≤ B) (hs : S ≤ i+j) :
    (planeVector i j,0)∈heightHull A B S := by
  have hs' : (S : ℝ)  ≤  (i : ℝ) + j := by exact_mod_cast hs
  have he := lattice_height_mem (S := S) hi hij
  change (planeVector i j,max ((S:ℝ)-i-j) 0)∈heightHull A B S at he
  simpa only [max_eq_right (by linarith : (S:ℝ)-i-j ≤ 0)] using he

 theorem lower_height_mem {A B S : ℕ} (hA : 0<A) (hS : 0<S) (hSB : S ≤ B)
    {p : MomentPlane} (hp : p∈closedTrapezoid A B) (hps : p 0+p 1 ≤ S) :
    (p,markedHeight S p)∈heightHull A B S := by
  have hm : 0 < min A S := lt_min hA hS
  have hms : min A S ≤ S := min_le_right _ _
  have hmc : ((min A S : ℕ) : ℝ) ≤ S := by exact_mod_cast hms
  have hp' : p∈closedTrapezoid (min A S : ℕ) S := by
    refine ⟨hp.1,?_,hp.2.2.1,hps⟩
    rw [Nat.cast_min]
    exact le_min hp.2.1 (by linarith [hp.2.2.1])
  have he := closedTrapezoid_mem_convexHull (by exact_mod_cast hm) hmc hp'
  have hc : Convex ℝ {q : MomentPlane | (q,(S:ℝ)-q 0-q 1)∈heightHull A B S} :=
    convex_affine_height_preimage (convex_convexHull ℝ _) S
  have hs : range (trapezoidCorners (min A S : ℕ) S)⊆
      {q : MomentPlane | (q,(S:ℝ)-q 0-q 1)∈heightHull A B S} := by
    rintro _ ⟨i,rfl⟩
    fin_cases i
    · simpa [trapezoidCorners,planeVector] using lattice_lower_mem (A := A) (B := B) (S := S)
        (i := 0) (j := 0) (by omega) (by omega) (by omega)
    · simpa [trapezoidCorners,planeVector] using lattice_lower_mem (A := A) (B := B) (S := S)
        (i := min A S) (j := 0) (by omega) (by omega) (by omega)
    · simpa [trapezoidCorners,planeVector,Nat.cast_sub hms] using
        lattice_lower_mem (A := A) (B := B) (S := S)
          (i := min A S) (j := S-min A S) (by omega) (by omega) (by omega)
    · simpa [trapezoidCorners,planeVector] using lattice_lower_mem (A := A) (B := B) (S := S)
        (i := 0) (j := S) (by omega) (by omega) (by omega)
  have h := convexHull_min hs hc he
  simpa only [mem_ofPred_eq,markedHeight,max_eq_left (by linarith : 0 ≤ (S:ℝ)-p 0-p 1)] using h

 theorem convex_diagonal_segment {T : Set MomentPlane} (hT : Convex ℝ T)
    {C D x : ℝ} (hC : 0<C) (hx0 : 0 ≤ x) (hxC : x ≤ C)
    (h0 : planeVector 0 D∈T) (h1 : planeVector C (D-C)∈T) :
    planeVector x (D-x)∈T := by
  have hl0 : 0 ≤ x/C := div_nonneg hx0 hC.le
  have hl1 : x/C ≤ 1 := (div_le_one hC).mpr hxC
  convert hT h0 h1 (sub_nonneg.mpr hl1) hl0 (by ring : (1-x/C)+x/C=1) using 1
  ext j
  fin_cases j
  all_goals simp [planeVector]
  all_goals field_simp
  all_goals ring

 theorem convex_horizontal_segment {T : Set MomentPlane} (hT : Convex ℝ T)
    {C D x y : ℝ} (hCD : C<D) (hxC : C ≤ x) (hxD : x ≤ D)
    (h0 : planeVector C y∈T) (h1 : planeVector D y∈T) :
    planeVector x y∈T := by
  have hl0 : 0 ≤ (x-C)/(D-C) := div_nonneg (sub_nonneg.mpr hxC) (sub_pos.mpr hCD).le
  have hl1 : (x-C)/(D-C) ≤ 1 := (div_le_one (sub_pos.mpr hCD)).mpr (by linarith)
  convert hT h0 h1 (sub_nonneg.mpr hl1) hl0
    (by ring : (1-(x-C)/(D-C))+(x-C)/(D-C)=1) using 1
  ext j
  fin_cases j
  all_goals simp [planeVector]
  all_goals field_simp [(sub_pos.mpr hCD).ne', (by linarith : -C+D≠0)]
  all_goals ring

 theorem convex_vertical_segment {T : Set MomentPlane} (hT : Convex ℝ T)
    {C D x y : ℝ} (hyC : C ≤ y) (hyD : y ≤ D)
    (h0 : planeVector x C∈T) (h1 : planeVector x D∈T) :
    planeVector x y∈T := by
  by_cases he : C=D
  · have hCy : C=y := by linarith
    rwa [←hCy]
  have hCD : C<D := lt_of_le_of_ne (hyC.trans hyD) he
  have hl0 : 0 ≤ (y-C)/(D-C) := div_nonneg (sub_nonneg.mpr hyC) (sub_pos.mpr hCD).le
  have hl1 : (y-C)/(D-C) ≤ 1 := (div_le_one (sub_pos.mpr hCD)).mpr (by linarith)
  convert hT h0 h1 (sub_nonneg.mpr hl1) hl0
    (by ring : (1-(y-C)/(D-C))+(y-C)/(D-C)=1) using 1
  ext j
  fin_cases j
  all_goals simp [planeVector]
  all_goals field_simp [(sub_pos.mpr hCD).ne', (by linarith : -C+D≠0)]
  all_goals ring

 theorem upper_height_mem {A B S : ℕ} (hA : 0<A) (hS : 0<S)
    (hAB : A ≤ B) (hSB : S ≤ B) {p : MomentPlane}
    (hp : p∈closedTrapezoid A B) (hps : (S:ℝ) ≤ p 0+p 1) :
    (p,markedHeight S p)∈heightHull A B S := by
  let T : Set MomentPlane := {q | (q,0)∈heightHull A B S}
  have hT : Convex ℝ T := convex_zero_height_preimage (convex_convexHull ℝ _)
  have hA' : (0:ℝ)<A := by exact_mod_cast hA
  have htop : planeVector (p 0) ((B:ℝ)-p 0)∈T := by
    apply convex_diagonal_segment hT hA' hp.1 hp.2.1
    · simpa only [T,mem_ofPred_eq,Nat.cast_zero] using lattice_upper_mem (A := A) (B := B) (S := S) (i := 0) (j := B) (by omega) (by omega) (by omega)
    · simpa only [T,mem_ofPred_eq,Nat.cast_sub hAB] using
        lattice_upper_mem (A := A) (B := B) (S := S) (i := A) (j := B-A) (by omega) (by omega) (by omega)
  have hbottom : planeVector (p 0) (max ((S:ℝ)-p 0) 0)∈T := by
    by_cases hx : p 0 ≤ (min A S : ℕ)
    · have hms : min A S ≤ S := min_le_right _ _
      have hmc : ((min A S : ℕ) : ℝ) ≤ S := by exact_mod_cast hms
      rw [max_eq_left (by linarith : 0 ≤ (S:ℝ)-p 0)]
      apply convex_diagonal_segment hT (by exact_mod_cast (lt_min hA hS)) hp.1 hx
      · simpa only [T,mem_ofPred_eq,Nat.cast_zero] using lattice_upper_mem (A := A) (B := B) (S := S) (i := 0) (j := S) (by omega) (by omega) (by omega)
      · simpa only [T,mem_ofPred_eq,Nat.cast_sub hms] using
          lattice_upper_mem (A := A) (B := B) (S := S) (i := min A S) (j := S-min A S)
            (by omega) (by omega) (by omega)
    · have hSA : S<A := by
        by_contra he
        have he' : min A S=A := min_eq_left (by omega)
        rw [he'] at hx
        exact hx hp.2.1
      have hxS : (S:ℝ)<p 0 := by simpa only [min_eq_right hSA.le] using lt_of_not_ge hx
      rw [max_eq_right (by linarith : (S:ℝ)-p 0 ≤ 0)]
      apply convex_horizontal_segment hT (by exact_mod_cast hSA) hxS.le hp.2.1
      · simpa only [T,mem_ofPred_eq,Nat.cast_zero] using lattice_upper_mem (A := A) (B := B) (S := S) (i := S) (j := 0) (by omega) (by omega) (by omega)
      · simpa only [T,mem_ofPred_eq,Nat.cast_zero] using lattice_upper_mem (A := A) (B := B) (S := S) (i := A) (j := 0) (by omega) (by omega) (by omega)
  have he := convex_vertical_segment hT (max_le (by linarith) hp.2.2.1)
    (by linarith [hp.2.2.2] : p 1 ≤ (B:ℝ)-p 0) hbottom htop
  have hpv : planeVector (p 0) (p 1)=p := by ext j; fin_cases j <;> rfl
  rw [hpv] at he
  simpa only [T,mem_ofPred_eq,markedHeight,max_eq_right (by linarith : (S:ℝ)-p 0-p 1 ≤ 0)] using he

 theorem markedHeight_feasible {A B S : ℕ} (hA : 0<A) (hS : 0<S)
    (hAB : A ≤ B) (hSB : S ≤ B) {p : MomentPlane} (hp : p∈closedTrapezoid A B) :
    ∃ h : TrapezoidWeight A B → ℝ,(∀ k,0 ≤ h k) ∧ (∑ k,h k)=1 ∧
      (∑ k,h k • trapezoidWeight A B k)=p ∧
      (∑ k,h k*markedHeight S (trapezoidWeight A B k))=markedHeight S p := by
  have hh : (p,markedHeight S p)∈heightHull A B S := by
    rcases le_total (p 0+p 1) (S:ℝ) with hs|hs
    · exact lower_height_mem hA hS hSB hp hs
    · exact upper_height_mem hA hS hAB hSB hp hs
  obtain ⟨h,hn,hs,he⟩ := convexHull_range_weights hh
  refine ⟨h,hn,hs,?_,?_⟩
  · simpa only [heightGraph,Prod.fst_sum,Prod.smul_fst] using congrArg Prod.fst he
  · simpa only [heightGraph,Prod.snd_sum,Prod.smul_snd,smul_eq_mul] using congrArg Prod.snd he

 theorem markedHeight_jensen {ι : Type*} [Fintype ι] {w : ι → MomentPlane}
    {q : ι → ℝ} {p : MomentPlane} (hq : ∀ i,0≤q i) (hs : ∑ i,q i=1)
    (he : ∑ i,q i • w i=p) (S : ℝ) :
    markedHeight S p≤∑ i,q i*markedHeight S (w i) := by
  have hcoord (j : Fin 2) : ∑ i,q i*(w i) j=p j := by
    have h := congrArg (fun z : MomentPlane => z j) he
    simpa using h
  have hsum : ∑ i,q i*(S-(w i) 0-(w i) 1)=S-p 0-p 1 := by
    simp only [mul_sub,Finset.sum_sub_distrib]
    rw [←Finset.sum_mul,hs,one_mul,hcoord 0,hcoord 1]
  apply max_le
  · rw [←hsum]
    exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (le_max_left _ _) (hq i))
  · exact Finset.sum_nonneg (fun i _ => mul_nonneg (hq i) (le_max_right _ _))

 theorem marked_gibbs_error {A B S : ℕ} (hA : 0<A) (hS : 0<S)
    (hAB : A≤B) (hSB : S≤B) {a : TrapezoidWeight A B → ℝ} {M l : ℝ}
    (ha : ∀ k,0<a k) (hloga : ∀ k,|Real.log (a k)|≤M) (hl : l<0)
    (x : MomentPlane) {p : MomentPlane} (hp : p∈closedTrapezoid A B)
    (hm : moment (trapezoidWeight A B)
      (fun k => a k*Real.exp (l*markedHeight S (trapezoidWeight A B k))) x=p) :
    0≤(∑ k,gibbs (trapezoidWeight A B)
      (fun j => a j*Real.exp (l*markedHeight S (trapezoidWeight A B j))) x k*
        markedHeight S (trapezoidWeight A B k))-markedHeight S p ∧
    (∑ k,gibbs (trapezoidWeight A B)
      (fun j => a j*Real.exp (l*markedHeight S (trapezoidWeight A B j))) x k*
        markedHeight S (trapezoidWeight A B k))-markedHeight S p
      ≤(2*M+Fintype.card (TrapezoidWeight A B))/(-l) := by
  have ha' (k : TrapezoidWeight A B) :
      0<a k*Real.exp (l*markedHeight S (trapezoidWeight A B k)) :=
    mul_pos (ha k) (Real.exp_pos _)
  constructor
  · exact sub_nonneg.mpr (markedHeight_jensen (fun k => (gibbs_pos ha' x k).le)
      (sum_gibbs ha' x) ((gibbs_mean x).trans hm) S)
  · obtain ⟨h,hn,hs,hmean,hheight⟩ := markedHeight_feasible hA hS hAB hSB hp
    have hbound := gibbs_tilt_height_bound ha hloga hn hs l x (hmean.trans hm.symm)
    rw [hheight] at hbound
    exact (le_div_iff₀ (neg_pos.mpr hl)).mpr (by simpa only [mul_comm] using hbound)

 theorem probability_affine_height {ι : Type*} [Fintype ι] {w : ι → MomentPlane}
    {q : ι → ℝ} {p : MomentPlane} (hs : ∑ i,q i=1)
    (he : ∑ i,q i • w i=p) (D c S : ℝ) :
    (∑ i,q i*(D-c*((w i) 0+(w i) 1)-markedHeight S (w i)))=
      D-c*(p 0+p 1)-(∑ i,q i*markedHeight S (w i)) := by
  have hcoord (j : Fin 2) : ∑ i,q i*(w i) j=p j := by
    have h := congrArg (fun z : MomentPlane => z j) he
    simpa using h
  calc
    _=(∑ i,q i*D)-c*(∑ i,q i*(w i) 0)-c*(∑ i,q i*(w i) 1)-
        (∑ i,q i*markedHeight S (w i)) := by
      simp only [Finset.mul_sum,←Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _=_ := by rw [←Finset.sum_mul,hs,one_mul,hcoord 0,hcoord 1]; ring

end PackingSufficiencySupport.FiniteMoment

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Manifold Topology
open Set Function Manifold MeasureTheory
section

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] [PreconnectedSpace M]
  {I : Type*} [Fintype I] {K : Set M}

theorem surface_partition_primitive_mod_bump (hpos : PositivePlaneTransitions M)
    (hK : IsCompact K) (B : I → SurfaceCoordinateBox M)
    (ρ : SmoothPartitionOfUnity I 𝓘(ℝ,Plane) M K) (hρ : ρ.IsSubordinate (fun i => (B i).carrier))
    {Ω : P → ManifoldTwoForm Plane M} (hΩ : SmoothTwoFormFamily Ω)
    (hskew : ∀ p x u v, Ω p x u v = -Ω p x v u)
    (hz : ∀ p x, x ∉ K → Ω p x=0)
    (B₀ : SurfaceCoordinateBox M) (β₀ : BoxUnitBump B₀) :
    HasCompactPrimitiveFamily (fun p => Ω p-partitionFormMass B ρ (Ω p) • β₀.form) := by
  classical
  let : MulActionWithZero ℝ (Plane →L[ℝ] Plane →L[ℝ] ℝ) :=
    @Module.toMulActionWithZero ℝ (Plane →L[ℝ] Plane →L[ℝ] ℝ) inferInstance inferInstance inferInstance
  let β (i : I) : BoxUnitBump (B i) := Classical.choice (B i).exists_unit_bump
  let Ωi := partitionTwoForm ρ Ω
  let Ki : I → Set M := fun i => K ∩ tsupport (ρ i)
  have hKi (i : I) : IsCompact (Ki i) := hK.inter_right (isClosed_tsupport (ρ i))
  have hKiB (i : I) : Ki i ⊆ (B i).carrier := fun _ hx => hρ i hx.2
  have hΩi (i : I) : SmoothTwoFormFamily (Ωi i) := partitionTwoForm_smooth ρ hΩ i
  have hzΩi (i : I) : ∀ p x, x ∉ Ki i → Ωi i p x=0 := partitionTwoForm_zero ρ hz i
  have hsΩi (i : I) : ∀ p x u v, Ωi i p x u v = -Ωi i p x v u :=
    partitionTwoForm_skew ρ hskew i
  let m : I → P → ℝ := fun i p => chartMass (B i).center (Ωi i p)
  have hm (i : I) : ContDiff ℝ ∞ (m i) :=
    chartMass_smooth (hΩi i (B i).center) (hKi i) (fun x hx => (hKiB i hx).1) (hzΩi i)
  have hlocal (i : I) : HasCompactPrimitiveFamily (fun p => Ωi i p-m i p • (β i).form) := by
    have hscaled : SmoothTwoFormFamily (fun p => m i p • (β i).form) :=
      (SmoothTwoFormFamily.const (β i).smooth).smul (hm i)
    have hdif : SmoothTwoFormFamily (fun p => Ωi i p-m i p • (β i).form) :=
      (hΩi i).sub hscaled
    apply surface_box_primitive hdif (fun p x u v => by
      change Ωi i p x u v - m i p * (β i).form x u v =
        -(Ωi i p x v u - m i p * (β i).form x v u)
      rw [hsΩi i p x u v,(β i).skew x u v]; ring)
      (B i) ((hKi i).union (β i).compact_supportSet)
      (union_subset (hKiB i) (β i).support_subset)
    · intro p x hx
      change Ωi i p x - m i p • (β i).form x=0
      rw [hzΩi i p x (fun hk => hx (Or.inl hk)),
        (β i).zero_off x (fun hk => hx (Or.inr hk))]
      apply ContinuousLinearMap.ext
      intro u
      apply ContinuousLinearMap.ext
      intro v
      change (0:ℝ)-m i p*0=0
      simp only [mul_zero,sub_self]
    · intro p
      have h1 := (hΩi i).eval p |>.coefficient_integrable (B i).center (hKi i)
        (fun x hx => (hKiB i hx).1) (hzΩi i p)
      have h2 := hscaled.eval p |>.coefficient_integrable (B i).center (β i).compact_supportSet
        (fun x hx => ((β i).support_subset hx).1)
        (fun x hx => by
          change m i p • (β i).form x=0
          rw [(β i).zero_off x hx]
          apply ContinuousLinearMap.ext
          intro firstVector
          apply ContinuousLinearMap.ext
          intro secondVector
          change m i p * 0=0
          exact mul_zero _)
      rw [chartMass_sub h1 h2,chartMass_smul,(β i).unit_mass,mul_one]
      exact sub_self _
  have hcommon (i : I) : HasCompactPrimitiveFamily (fun p => Ωi i p-m i p • β₀.form) := by
    have ht := (surface_bump_difference (P := P) hpos (β i) β₀).smul (hm i)
    have he : (fun p => Ωi i p-m i p • (β i).form)+
        (fun p => m i p • ((β i).form-β₀.form)) =
          (fun p => Ωi i p-m i p • β₀.form) := by
      funext p x
      apply ContinuousLinearMap.ext
      intro u
      apply ContinuousLinearMap.ext
      intro v
      change Ωi i p x u v - m i p * (β i).form x u v +
        m i p * ((β i).form x u v - β₀.form x u v) =
          Ωi i p x u v - m i p * β₀.form x u v
      ring
    exact he ▸ (hlocal i).add ht
  have hall := HasCompactPrimitiveFamily.sum Finset.univ (fun i _ => hcommon i)
  have he : (∑ i, fun p => Ωi i p-m i p • β₀.form)=
      (fun p => Ω p-partitionFormMass B ρ (Ω p) • β₀.form) := by
    funext p x
    apply ContinuousLinearMap.ext
    intro u
    apply ContinuousLinearMap.ext
    intro v
    simp only [Finset.sum_apply,sum_apply,Pi.sub_apply,Pi.smul_apply,
      sub_apply,smul_apply,smul_eq_mul]
    rw [Finset.sum_sub_distrib,← Finset.sum_mul]
    change (∑ i, Ωi i p x u v) - (∑ i, m i p) * β₀.form x u v =
      Ω p x u v - (∑ i, m i p) * β₀.form x u v
    congr 1
    have hh := congrArg (fun F : P → ManifoldTwoForm Plane M => F p x u v)
      (partitionTwoForm_sum ρ hz)
    simpa only [Finset.sum_apply,sum_apply] using hh
  exact he ▸ hall

end
section

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold 𝓘(ℝ,Plane) ∞ M] [T2Space M] [PreconnectedSpace M]
  [NormalSpace M] [SigmaCompactSpace M]

theorem exists_primitive_near_proper_compact {K : Set M} (hK : IsCompact K)
    (hproper : Kᶜ.Nonempty) (hor : PositivePlaneTransitions M)
    {Ω : P → ManifoldTwoForm Plane M} (hΩ : SmoothTwoFormFamily Ω)
    (hskew : ∀ p x u v,Ω p x u v= -Ω p x v u) :
    ∃ (α : P → ManifoldOneForm Plane M) (L : Set M), IsCompact L ∧
      SmoothOneFormFamily α ∧ (∀ p x,x∉L → α p x=0) ∧
      ∀ᶠ x in 𝓝ˢ K,∀ p,manifoldExteriorOneForm (α p) x=Ω p x := by
  classical
  let : MulActionWithZero ℝ (Plane →L[ℝ] Plane →L[ℝ] ℝ) :=
    @Module.toMulActionWithZero ℝ (Plane →L[ℝ] Plane →L[ℝ] ℝ) inferInstance inferInstance inferInstance
  obtain ⟨x,hx⟩ := hproper
  obtain ⟨B₀,_hB₀,hB₀K⟩ := SurfaceCoordinateBox.exists_compactCarrier_subset hK.isClosed.isOpen_compl hx
  obtain ⟨β₀⟩ := B₀.exists_unit_bump
  obtain ⟨χ,hχ,hχc,_,hχ1,_⟩ := exists_smooth_manifold_cutoff (E := Plane) hK isOpen_univ (subset_univ K)
  let Ξ : P → ManifoldTwoForm Plane M := fun p y => χ y • Ω p y
  have hΞ : SmoothTwoFormFamily Ξ := hΩ.spatial_smul hχ
  have hsΞ : ∀ p y u v,Ξ p y u v= -Ξ p y v u := by
    intro p y u v
    change χ y * Ω p y u v= -(χ y * Ω p y v u)
    rw [hskew p y u v,mul_neg]
  have hzΞ : ∀ p y,y∉tsupport χ → Ξ p y=0 := by
    intro p y hy
    dsimp only [Ξ]
    rw [image_eq_zero_of_notMem_tsupport hy,zero_smul]
  obtain ⟨s,ρ,hρ⟩ := SurfaceCoordinateBox.finite_partition hχc
  obtain ⟨L,hL,α,hα,hαz,hdα⟩ := surface_partition_primitive_mod_bump hor hχc
    (fun B : s => B.1) ρ hρ hΞ hsΞ hzΞ B₀ β₀
  have hprim : IsPrimitiveFamily
      (fun p => Ξ p-partitionFormMass (fun B : s => B.1) ρ (Ξ p) • β₀.form) α := ⟨hα,hdα⟩
  have hKβ : K⊆β₀.supportSetᶜ := by
    intro y hy hyβ
    exact hB₀K (B₀.carrier_subset_compactCarrier (β₀.support_subset hyβ)) hy
  have hβzero : β₀.supportSetᶜ∈𝓝ˢ K :=
    β₀.compact_supportSet.isClosed.isOpen_compl.mem_nhdsSet.mpr hKβ
  refine ⟨α,L,hL,hα,hαz,?_⟩
  filter_upwards [hχ1,hβzero] with y hyχ hyβ
  intro p
  have hprimAt : manifoldExteriorOneForm (α p) y =
      Ξ p y-partitionFormMass (fun B : s => B.1) ρ (Ξ p) • β₀.form y := by
    have hySource := mem_extChartAt_source (I := 𝓘(ℝ,Plane)) y
    have hinvertible : (chartDifferential (E := Plane) y y).IsInvertible := by
      convert! isInvertible_mfderiv_extChartAt (I := 𝓘(ℝ,Plane)) hySource using 1
    rw [manifoldExteriorOneForm,
      hprim.exterior p y _ ((extChartAt 𝓘(ℝ,Plane) y).map_source hySource)]
    simp only [chartTwoForm,(extChartAt 𝓘(ℝ,Plane) y).left_inv hySource]
    apply ContinuousLinearMap.ext
    intro firstVector
    apply ContinuousLinearMap.ext
    intro secondVector
    simp only [ContinuousLinearMap.bilinearComp_apply,hinvertible.inverse_apply_self]
    rfl
  rw [hprimAt]
  change χ y • Ω p y-partitionFormMass (fun B : s => B.1) ρ (Ξ p) • β₀.form y=Ω p y
  rw [hyχ,one_smul,β₀.zero_off y hyβ]
  apply ContinuousLinearMap.ext
  intro u
  apply ContinuousLinearMap.ext
  intro v
  change Ω p y u v-partitionFormMass (fun B : s => B.1) ρ (Ξ p)*0=Ω p y u v
  simp only [mul_zero,sub_zero]

end

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]

theorem extendedChartCoefficient_zero_form (c : M) (y : Plane) :
    extendedChartCoefficient c (fun _ : ℝ => (0 : ManifoldTwoForm Plane M)) (0,y)=0 := by
  unfold extendedChartCoefficient spatialZeroExtension
  split_ifs <;> simp only [chartTwoForm_zero,zero_apply]

theorem extendedChartCoefficient_sum {I : Type*} (s : Finset I) (c : M)
    (Ω : I → ManifoldTwoForm Plane M) (y : Plane) :
    extendedChartCoefficient c (fun _ : ℝ => ∑ i ∈ s, Ω i) (0,y) =
      ∑ i ∈ s, extendedChartCoefficient c (fun _ : ℝ => Ω i) (0,y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty,extendedChartCoefficient_zero_form]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi,Finset.sum_insert hi,extendedChartCoefficient_add,ih]

theorem chartMass_sum {I : Type*} (s : Finset I) (c : M)
    (Ω : I → ManifoldTwoForm Plane M)
    (hΩ : ∀ i ∈ s, Integrable (fun y => extendedChartCoefficient c (fun _ : ℝ => Ω i) (0,y))) :
    chartMass c (∑ i ∈ s, Ω i) = ∑ i ∈ s, chartMass c (Ω i) := by
  unfold chartMass
  simp_rw [extendedChartCoefficient_sum]
  exact integral_finsetSum s hΩ

end PackingSufficiencySupport.Hamiltonian
end

end OAI
