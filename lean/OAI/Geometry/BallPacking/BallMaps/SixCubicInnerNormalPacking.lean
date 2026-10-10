import Mathlib
import OAI.Geometry.BallPacking.BallMaps.SphereCartesianDescent

namespace OAI

noncomputable section

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators Pointwise
open Set Function Filter Manifold MeasureTheory
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment MomentPolytope
open FiniteMoment.Radial

 theorem actual_six_cubic_inner_normal_packing {N : ℕ} [Nonempty (Fin N)]
    (r r' : Fin N → ℝ) (hr : ∀ i,0<r i) (hr' : ∀ i,0≤r' i)
    (hrr : ∀ i,r' i<r i) {a : ℚ} (ha : (1:ℚ)/2<a) (ha1 : a<1)
    (hrs : ∀ i,r i<1-(a:ℝ)) (hvol : ∑ i,r i^3<1-(a:ℝ)^3) :
    ∃ L A B D S : ℕ,0<L ∧ 0<A ∧ 0<S ∧ A<S ∧ A≤B ∧ S≤B ∧ 3*B<D ∧ 3*S<D ∧
      (D:ℝ)=(L:ℝ)*(2-(a:ℝ)) ∧ (S:ℝ)=(L:ℝ)*(1-(a:ℝ)) ∧
      ∃ h₁ h₂ : ℚ, (∀ i,r i<h₁) ∧ h₁<h₂ ∧
        (h₁:ℝ)<(A:ℝ)/L ∧ (h₂:ℝ)<(B:ℝ)/L ∧
        ∃ ℓ,∃ φ : Fin N → Ambient 3 → BaseCurve × PlanePhase (Fin 2),
          (∀ i,FormNeighborhoodEmbedding (closedBall 3 (r' i)) (fun _ => successorStandardForm 2)
            (globalHorizontalCoupling phaseArea
              (physicalPrimitive (A := A) (B := B) D S (1/((L:ℝ)*Real.pi)) L ∘ planeMoments)) (φ i)) ∧
          (∀ i,MapsTo (φ i) (closedBall 3 (r' i))
            (interior (cubicExhaustion ℓ ×ˢ planeRegion sixModelBounds ![h₁,h₂]))) ∧
          Pairwise (fun i j => Disjoint (φ i '' closedBall 3 (r' i)) (φ j '' closedBall 3 (r' j))) := by
  have ha' : (1:ℝ)/2<(a:ℝ) := by
    have hh : (((1:ℚ)/2:ℚ):ℝ)<(a:ℝ) := Rat.cast_lt.mpr ha
    norm_num at hh ⊢
    exact hh
  have ha1' : (a:ℝ)<1 := by exact_mod_cast ha1
  obtain ⟨h₁,e,d₁,h₂,d₂,τ,ε,hrh,hhe,hes,hsd,hdh,hhd,hd₂,hh₁,hh₂,hτ,hτ1,hε,
      _hcap,hconc,hmean,houter⟩ := exists_six_model_comparison_data r hr ha' ha1' hrs hvol
  have hsd' : 1-a<d₁ := by exact_mod_cast hsd
  have hd₂' : d₂<(2-a)/3 := by exact_mod_cast hd₂
  obtain ⟨L,A,B,D,S,hL,hA,hS0,hAS,hAB,hSB,hB,hS,heA,heB,heD,heS⟩ :=
    exists_six_cubic_inner_weights ha ha1
      (show 0<e by exact_mod_cast (hh₁.trans (show (h₁:ℝ)<e by exact_mod_cast hhe)))
      (show e<1-a by exact_mod_cast hes)
      (hsd'.trans (hdh.trans hhd)) hd₂'
  have hLr : 0<(L:ℝ) := Nat.cast_pos.mpr hL
  have hh₁d : (h₁:ℝ)<d₁ := (show (h₁:ℝ)<e by exact_mod_cast hhe).trans (hes.trans hsd)
  have hh₂d : (h₂:ℝ)<d₂ := by exact_mod_cast hhd
  have hh₁₂ : h₁<h₂ := by
    have hh : (h₁:ℝ)<h₂ := hh₁d.trans (show (d₁:ℝ)<h₂ by exact_mod_cast hdh)
    exact_mod_cast hh
  have hh₁₂' : (h₁:ℝ)<h₂ := by exact_mod_cast hh₁₂
  have hPS := physicalParameter_maps_six_region hL (show (h₁:ℝ)<e by exact_mod_cast hhe) hh₂d heA heB
  have harea := physicalArea_eq_sixModelDensity hL heD heS
  have hsimp i p (hp : ∀ j,0≤p j) (ht : (∑ j,p j)≤r i) :
      p∈region sixModelBounds ![(h₁:ℝ),(h₂:ℝ)] :=
    sixModelRegion_contains_cap (hrh i).le ((hrh i).trans hh₁₂').le ⟨hp,ht⟩
  have hface (i : Fin N) (p : Moments 2) (hp : ∀ j,0≤p j) (ht : (∑ j,p j)≤r i) ν :
      (∑ j,sixModelBounds ν j*p j)≠![(h₁:ℝ),(h₂:ℝ)] ν := by
    have hs : p 0+p 1≤r i := by simpa only [Fin.sum_univ_two] using ht
    fin_cases ν
    · simp only [sixModelBounds,Fin.sum_univ_two]
      change 1*p 0+0*p 1≠(h₁:ℝ)
      exact ne_of_lt (by linarith [hp 1,hrh i])
    · simp only [sixModelBounds,Fin.sum_univ_two]
      change 1*p 0+1*p 1≠(h₂:ℝ)
      exact ne_of_lt (by simpa only [one_mul] using hs.trans_lt ((hrh i).trans hh₁₂'))
  obtain ⟨ℓ,Γ,_hΓ,he,φ,hφ,hm,hd⟩ := actual_cubic_representative_packing hA hS0 hAB hSB hB hS
    (one_div_pos.mpr (mul_pos hLr Real.pi_pos)) sixModelBounds ![(h₁:ℝ),(h₂:ℝ)]
    sixModelBounds_nonneg (by intro ν; fin_cases ν; exact hh₁; exact hh₂)
    (sixModelRegion_isCompact h₁ h₂) hPS r r' hr' hrr hsimp hface
    (by rw [harea]; exact hconc)
    (by rw [harea]; exact hmean) hτ hτ1 hε
    (by rw [harea]; exact houter)
  refine ⟨L,A,B,D,S,hL,hA,hS0,hAS,hAB,hSB,hB,hS,heD,heS,h₁,h₂,hrh,hh₁₂,?_,?_,ℓ,φ,?_,hm,hd⟩
  · rw [heA,mul_div_cancel_left₀ _ hLr.ne']
    exact_mod_cast hhe
  · rw [heB,mul_div_cancel_left₀ _ hLr.ne']
    exact hh₂d
  · intro i
    exact (hφ i).congr_target_near (fun x hx => interior_subset (hm i hx))
      (physicalCoupling_representative_near hLr.le hPS he)

 theorem actual_six_cubic_inner_polynomial_packing_avoid_axes {N : ℕ} [Nonempty (Fin N)]
    (r r' : Fin N → ℝ) (hr : ∀ i,0<r i) (hr' : ∀ i,0≤r' i)
    (hrr : ∀ i,r' i<r i) {a : ℚ} (ha : (1:ℚ)/2<a) (ha1 : a<1)
    (hrs : ∀ i,r i<1-(a:ℝ)) (hvol : ∑ i,r i^3<1-(a:ℝ)^3) :
    ∃ L A B D S : ℕ,0<L ∧ 0<A ∧ 0<S ∧ A<S ∧ A≤B ∧ S≤B ∧ 3*B<D ∧ 3*S<D ∧
      (D:ℝ)=(L:ℝ)*(2-(a:ℝ)) ∧ (S:ℝ)=(L:ℝ)*(1-(a:ℝ)) ∧
      ∃ t : ℝ,0<t ∧ ∃ f : Fin N → Ambient 3 → CubicAmbient,
        (∀ i,FormNeighborhoodEmbedding (closedBall 3 (r' i)) (fun _ => successorStandardForm 2)
          (cubicAmbientForm (A := A) (B := B) D S (1/((L:ℝ)*Real.pi)) t) (f i)) ∧
        (∀ i,MapsTo (f i) (closedBall 3 (r' i)) cubicAffineDomain) ∧
        Pairwise (fun i j => Disjoint (f i '' closedBall 3 (r' i)) (f j '' closedBall 3 (r' j))) := by
  classical
  obtain ⟨L,A,B,D,S,hL,hA,hS0,hAS,hAB,hSB,hB,hS,heD,heS,h₁,h₂,_hrh,_hh₁₂,hh₁,hh₂,ℓ,φ,hφ,hm,hd⟩ :=
    actual_six_cubic_inner_normal_packing r r' hr hr' hrr ha ha1 hrs hvol
  have hLr : 0<(L:ℝ) := Nat.cast_pos.mpr hL
  let K : Set CubicPhysicalSpace := ⋃ i,φ i '' closedBall 3 (r' i)
  have hK : IsCompact K := by
    apply isCompact_iUnion
    intro i
    obtain ⟨U,_hU,hKU,hs,_he,_hf⟩ := hφ i
    exact (closedBall_isCompact 3 (r' i)).image_of_continuousOn (hs.continuousOn.mono hKU)
  have hPS := physicalParameter_maps_six_region hL hh₁ hh₂
    (show (A:ℝ)=(L:ℝ)*((A:ℝ)/L) by field_simp)
    (show (B:ℝ)=(L:ℝ)*((B:ℝ)/L) by field_simp)
  have hKd (p : CubicPhysicalSpace) (hp : p∈K) :
      physicalParameter L (planeMoments p.2)∈Radial.lowerTrapezoid A B := by
    obtain ⟨i,x,hx,rfl⟩ := mem_iUnion.mp hp
    exact hPS (interior_subset (hm i hx)).2
  have hinv (p : CubicPhysicalSpace) (hp : p∈K) :
      (cubicPhysicalForm (A := A) (B := B) D S L p).IsInvertible := by
    obtain ⟨i,x,hx,rfl⟩ := mem_iUnion.mp hp
    exact (hφ i).target_invertible (complexSplitPhase 2).toLinearEquiv.finrank_eq hx
      (successorStandardForm_isInvertible 2)
  obtain ⟨t,ht,g,W,hW,hKW,hg,hgemb,hgT,hgform⟩ :=
    exists_actual_cubic_normal_transfer_into hA hAB D S hLr hK hKd hinv
      cubicAffineDomain_isOpen inclusion_mem_cubicAffineDomain
  obtain ⟨hf,hdj⟩ := postcompose_form_packing (fun i => closedBall 3 (r' i))
    (fun _ => successorStandardForm 2) (cubicPhysicalForm (A := A) (B := B) D S L)
    (cubicAmbientForm (A := A) (B := B) D S (1/((L:ℝ)*Real.pi)) t)
    hW g hg.contMDiffOn hgemb hgform φ hφ
    (fun i x hx => hKW (mem_iUnion.mpr ⟨i,x,hx,rfl⟩)) hd
  exact ⟨L,A,B,D,S,hL,hA,hS0,hAS,hAB,hSB,hB,hS,heD,heS,t,ht,fun i => g ∘ φ i,hf,fun i x hx => hgT (hKW (mem_iUnion.mpr ⟨i,x,hx,rfl⟩)),hdj⟩

 theorem actual_six_cubic_inner_polynomial_packing {N : ℕ} [Nonempty (Fin N)]
    (r r' : Fin N → ℝ) (hr : ∀ i,0<r i) (hr' : ∀ i,0≤r' i)
    (hrr : ∀ i,r' i<r i) {a : ℚ} (ha : (1:ℚ)/2<a) (ha1 : a<1)
    (hrs : ∀ i,r i<1-(a:ℝ)) (hvol : ∑ i,r i^3<1-(a:ℝ)^3) :
    ∃ L A B D S : ℕ,0<L ∧ 0<A ∧ 0<S ∧ A<S ∧ A≤B ∧ S≤B ∧ 3*B<D ∧ 3*S<D ∧
      (D:ℝ)=(L:ℝ)*(2-(a:ℝ)) ∧ (S:ℝ)=(L:ℝ)*(1-(a:ℝ)) ∧
      ∃ t : ℝ,0<t ∧ ∃ f : Fin N → Ambient 3 → CubicAmbient,
        (∀ i,FormNeighborhoodEmbedding (closedBall 3 (r' i)) (fun _ => successorStandardForm 2)
          (cubicAmbientForm (A := A) (B := B) D S (1/((L:ℝ)*Real.pi)) t) (f i)) ∧
        Pairwise (fun i j => Disjoint (f i '' closedBall 3 (r' i)) (f j '' closedBall 3 (r' j))) := by
  obtain ⟨L,A,B,D,S,hL,hA,hS0,hAS,hAB,hSB,hB,hS,heD,heS,t,ht,f,hf,_hinto,hd⟩ :=
    actual_six_cubic_inner_polynomial_packing_avoid_axes r r' hr hr' hrr ha ha1 hrs hvol
  exact ⟨L,A,B,D,S,hL,hA,hS0,hAS,hAB,hSB,hB,hS,heD,heS,t,ht,f,hf,hd⟩

 theorem actual_six_quadric_polynomial_packing {N : ℕ} [Nonempty (Fin N)]
    (r r' : Fin N → ℝ) (hr : ∀ i,0<r i) (hr' : ∀ i,0≤r' i)
    (hrr : ∀ i,r' i<r i) {a : ℚ} (ha : (1:ℚ)/2<a) (ha1 : a<1)
    (hrs : ∀ i,r i<1-(a:ℝ)) (hvol : ∑ i,r i^3<1-(a:ℝ)^3) :
    ∃ L A B S : ℕ,0<L ∧ 0<A ∧ 0<S ∧ A<S ∧ A≤B ∧ S≤B ∧ 3*B<L+S ∧ 2*S<L ∧
      (S:ℝ)=(L:ℝ)*(1-(a:ℝ)) ∧
      ∃ t δ : ℝ,0<t ∧ 0<δ ∧ ∃ f : Fin N → Ambient 3 → CubicAmbient,
        (∀ i,FormNeighborhoodEmbedding (closedBall 3 (r' i)) (fun _ => successorStandardForm 2)
          (outerAmbientForm (A := A) (B := B) L S (1/((L:ℝ)*Real.pi)) t δ) (f i)) ∧
        (∀ i,∀ x∈closedBall 3 (r' i),(f i x).2≠0) ∧
        Pairwise (fun i j => Disjoint (f i '' closedBall 3 (r' i)) (f j '' closedBall 3 (r' j))) := by
  classical
  obtain ⟨L,A,B,D,S,hL,hA,hS0,hAS,hAB,hSB,hB,_hS,heD,heS,t,ht,f,hf,hinto,hd⟩ :=
    actual_six_cubic_inner_polynomial_packing_avoid_axes r r' hr hr' hrr ha ha1 hrs hvol
  have hLr : 0<(L:ℝ) := Nat.cast_pos.mpr hL
  have hDL : D=L+S := by
    apply Nat.cast_injective (R := ℝ)
    push_cast
    rw [heD,heS]
    ring
  subst D
  have hSL : 2*S<L := by
    have har : (1:ℝ)/2<(a:ℝ) := by
      have hh : (((1:ℚ)/2:ℚ):ℝ)<(a:ℝ) := Rat.cast_lt.mpr ha
      norm_num at hh ⊢
      exact hh
    have hrS : 2*(S:ℝ)<(L:ℝ) := by rw [heS]; nlinarith
    exact_mod_cast hrS
  let K : Set CubicAmbient := ⋃ i,f i '' closedBall 3 (r' i)
  have hK : IsCompact K := by
    apply isCompact_iUnion
    intro i
    obtain ⟨U,_hU,hKU,hs,_he,_hf⟩ := hf i
    exact (closedBall_isCompact 3 (r' i)).image_of_continuousOn (hs.continuousOn.mono hKU)
  have hKd : K⊆cubicAffineDomain := by
    intro p hp
    obtain ⟨i,x,hx,rfl⟩ := mem_iUnion.mp hp
    exact hinto i hx
  have hdim : Module.finrank ℝ (Ambient 3)=Module.finrank ℝ CubicAmbient := by
    simp [Ambient,CubicAmbient,PlaneBase,Module.finrank_pi_fintype,Complex.finrank_real_complex]
  have hinv (p : CubicAmbient) (hp : p∈K) :
      (cubicAmbientForm (A := A) (B := B) (L+S) S (1/((L:ℝ)*Real.pi)) t p).IsInvertible := by
    obtain ⟨i,x,hx,rfl⟩ := mem_iUnion.mp hp
    exact (hf i).target_invertible hdim hx (successorStandardForm_isInvertible 2)
  obtain ⟨δ,hδ,g,W,hW,hKW,hg,he,hgT,hgform⟩ :=
    exists_actual_outer_normal_transfer hAS hSL hB (1/((L:ℝ)*Real.pi)) t hK hKd hinv
  obtain ⟨hgφ,hdj⟩ := postcompose_form_packing (fun i => closedBall 3 (r' i))
    (fun _ => successorStandardForm 2)
    (cubicAmbientForm (A := A) (B := B) (L+S) S (1/((L:ℝ)*Real.pi)) t)
    (outerAmbientForm (A := A) (B := B) L S (1/((L:ℝ)*Real.pi)) t δ)
    hW g hg.contMDiff.contMDiffOn he (by
      intro x hx v w
      have hh := hgform x hx v w
      simp only [mfderiv_eq_fderiv]
      convert! hh using 1) f hf
    (fun i x hx => hKW (mem_iUnion.mpr ⟨i,x,hx,rfl⟩)) hd
  exact ⟨L,A,B,S,hL,hA,hS0,hAS,hAB,hSB,hB,hSL,heS,t,δ,ht,hδ,fun i => g ∘ f i,
    hgφ,fun i x hx => hgT (f i x) (hKW (mem_iUnion.mpr ⟨i,x,hx,rfl⟩)),hdj⟩

 def cubicOuterBubbleForm {A B : ℕ} (L S m p N : ℕ) (t δ c : ℝ) (D : ℝ → ℝ) (ε : ℝ) :=
   euclideanExteriorOneForm (cubicOuterBubblePrimitive (A := A) (B := B) L S m p N t δ c D ε)

 theorem exists_uniform_outer_bubble_transfer {A B L S m p N : ℕ} (hmp : m<p) (hN : 0<N)
     (t δ c : ℝ) {D : ℝ → ℝ} (hD : ContDiff ℝ ∞ D) (hD0 : (L:ℝ)*D 0=1)
     {K : Set CubicAmbient} (hK : IsCompact K)
     (hinv : ∀ x∈K,(outerAmbientForm (A := A) (B := B) L S (D 0*c) t δ x).IsInvertible)
     {T : Set CubicAmbient} (hT : IsOpen T) (hKT : K⊆T) {η : ℝ} (hη : 0<η) :
     ∃ τ>0,τ≤η ∧ ∀ ε∈Ioc (0:ℝ) τ,∃ g : CubicAmbient → CubicAmbient,∃ W,
       IsOpen W ∧ K⊆W ∧ ContDiff ℝ ∞ g ∧ Topology.IsEmbedding (fun x : W => g x.val) ∧
       MapsTo g W T ∧ ∀ x∈W,∀ v w,
       cubicOuterBubbleForm (A := A) (B := B) L S m p N t δ c D ε
         (g x) (fderiv ℝ g x v) (fderiv ℝ g x w)=
       outerAmbientForm (A := A) (B := B) L S (D 0*c) t δ x v w := by
   let Γ := cubicOuterBubblePrimitive (A := A) (B := B) L S m p N t δ c D
   have he0 (x : CubicAmbient) : manifoldExteriorOneForm (Γ 0) x=
       outerAmbientForm (A := A) (B := B) L S (D 0*c) t δ x := by
     change manifoldExteriorOneForm (cubicOuterBubblePrimitive (A := A) (B := B) L S m p N t δ c D 0) x=_
     rw [cubicOuterBubblePrimitive_zero hmp hN t δ c hD0,vector_exteriorOneForm]
     rfl
   have hid : ContMDiff ((𝓘(ℝ,ℝ)).prod 𝓘(ℝ,CubicAmbient)) 𝓘(ℝ,CubicAmbient) ∞
       (fun a : ℝ×CubicAmbient => a.2) := contMDiff_snd
   obtain ⟨τ,hτ,hτη,hall⟩ := exists_uniform_compact_exact_fibre_embedding_central_into
     (cubicOuterBubblePrimitive_smooth_family (A := A) (B := B) L S m p N t δ c hD) hK
     (by intro x hx; rw [he0]; exact hinv x hx) isOpen_univ (subset_univ K) hη hid
     (fun _ _ => Topology.IsEmbedding.subtypeVal) hT hKT
     (fun ε => cubicOuterBubbleForm (A := A) (B := B) L S m p N t δ c D ε) (by
       intro ε _ x _
       apply ContinuousLinearMap.ext
       intro v
       apply ContinuousLinearMap.ext
       intro w
       simp only [manifoldMapDifferential,mfderiv_eq_fderiv,fderiv_fun_id,
         vector_exteriorOneForm,ContinuousLinearMap.bilinearComp_apply,ContinuousLinearMap.id_apply]
       rfl)
   refine ⟨τ,hτ,hτη,?_⟩
   intro ε hε
   obtain ⟨g,W,hW,hKW,hg,he,hgT,hgf⟩ := hall ε hε
   refine ⟨g,W,hW,hKW,hg.contDiff,he,hgT,?_⟩
   intro x hx v w
   have hh := hgf x hx v w
   rw [he0] at hh
   simp only [mfderiv_eq_fderiv] at hh
   convert! hh using 1

 theorem outer_packing_uniform_bubble {A B L S m p N k : ℕ} (hmp : m<p) (hN : 0<N)
     (t δ c : ℝ) {D : ℝ → ℝ} (hD : ContDiff ℝ ∞ D) (hD0 : (L:ℝ)*D 0=1)
     (r : Fin k → ℝ) (f : Fin k → Ambient 3 → CubicAmbient)
     (hf : ∀ i,FormNeighborhoodEmbedding (closedBall 3 (r i)) (fun _ => successorStandardForm 2)
       (outerAmbientForm (A := A) (B := B) L S (D 0*c) t δ) (f i))
     (hinto : ∀ i,∀ x∈closedBall 3 (r i),(f i x).2≠0)
     (hd : Pairwise (fun i j => Disjoint (f i '' closedBall 3 (r i)) (f j '' closedBall 3 (r j))))
     {η : ℝ} (hη : 0<η) :
     ∃ τ>0,τ≤η ∧ ∀ ε∈Ioc (0:ℝ) τ,∃ g : Fin k → Ambient 3 → CubicAmbient,
       (∀ i,FormNeighborhoodEmbedding (closedBall 3 (r i)) (fun _ => successorStandardForm 2)
         (cubicOuterBubbleForm (A := A) (B := B) L S m p N t δ c D ε) (g i)) ∧
       (∀ i,∀ x∈closedBall 3 (r i),(g i x).2≠0) ∧
       Pairwise (fun i j => Disjoint (g i '' closedBall 3 (r i)) (g j '' closedBall 3 (r j))) := by
   let K : Set CubicAmbient := ⋃ i,f i '' closedBall 3 (r i)
   have hK : IsCompact K := by
     apply isCompact_iUnion
     intro i
     obtain ⟨U,_hU,hKU,hs,_he,_hf⟩ := hf i
     exact (closedBall_isCompact 3 (r i)).image_of_continuousOn (hs.continuousOn.mono hKU)
   have hKT : K⊆{x : CubicAmbient | x.2≠0} := by
     intro x hx
     obtain ⟨i,y,hy,rfl⟩ := mem_iUnion.mp hx
     exact hinto i y hy
   have hdim : Module.finrank ℝ (Ambient 3)=Module.finrank ℝ CubicAmbient := by
     simp [Ambient,CubicAmbient,PlaneBase,Module.finrank_pi_fintype,Complex.finrank_real_complex]
   have hinv (x : CubicAmbient) (hx : x∈K) :
       (outerAmbientForm (A := A) (B := B) L S (D 0*c) t δ x).IsInvertible := by
     obtain ⟨i,y,hy,rfl⟩ := mem_iUnion.mp hx
     exact (hf i).target_invertible hdim hy (successorStandardForm_isInvertible 2)
   obtain ⟨τ,hτ,hτη,hall⟩ := exists_uniform_outer_bubble_transfer hmp hN t δ c hD hD0 hK hinv
     (isOpen_ne_fun continuous_snd continuous_const) hKT hη
   refine ⟨τ,hτ,hτη,?_⟩
   intro ε hε
   obtain ⟨g,W,hW,hKW,hg,he,hgT,hgf⟩ := hall ε hε
   obtain ⟨hcomp,hdj⟩ := postcompose_form_packing (fun i => closedBall 3 (r i))
     (fun _ => successorStandardForm 2)
     (outerAmbientForm (A := A) (B := B) L S (D 0*c) t δ)
     (cubicOuterBubbleForm (A := A) (B := B) L S m p N t δ c D ε)
     hW g hg.contMDiff.contMDiffOn he (by
       intro x hx v w
       simp only [mfderiv_eq_fderiv]
       convert! hgf x hx v w using 1) f hf
     (fun i x hx => hKW (mem_iUnion.mpr ⟨i,x,hx,rfl⟩)) hd
   exact ⟨fun i => g ∘ f i,hcomp,
     fun i x hx => hgT (hKW (mem_iUnion.mpr ⟨i,x,hx,rfl⟩)),hdj⟩

 theorem outer_packing_uniform_bubble_into {A B L S m p N k : ℕ} (hmp : m<p) (hN : 0<N)
     (t δ c : ℝ) {D : ℝ → ℝ} (hD : ContDiff ℝ ∞ D) (hD0 : (L:ℝ)*D 0=1)
     {T : Set CubicAmbient} (hT : IsOpen T)
     (r : Fin k → ℝ) (f : Fin k → Ambient 3 → CubicAmbient)
     (hf : ∀ i,FormNeighborhoodEmbedding (closedBall 3 (r i)) (fun _ => successorStandardForm 2)
       (outerAmbientForm (A := A) (B := B) L S (D 0*c) t δ) (f i))
     (hinto : ∀ i,MapsTo (f i) (closedBall 3 (r i)) T)
     (hd : Pairwise (fun i j => Disjoint (f i '' closedBall 3 (r i)) (f j '' closedBall 3 (r j))))
     {η : ℝ} (hη : 0<η) :
     ∃ τ>0,τ≤η ∧ ∀ ε∈Ioc (0:ℝ) τ,∃ g : Fin k → Ambient 3 → CubicAmbient,
       (∀ i,FormNeighborhoodEmbedding (closedBall 3 (r i)) (fun _ => successorStandardForm 2)
         (cubicOuterBubbleForm (A := A) (B := B) L S m p N t δ c D ε) (g i)) ∧
       (∀ i,MapsTo (g i) (closedBall 3 (r i)) T) ∧
       Pairwise (fun i j => Disjoint (g i '' closedBall 3 (r i)) (g j '' closedBall 3 (r j))) := by
   let K : Set CubicAmbient := ⋃ i,f i '' closedBall 3 (r i)
   have hK : IsCompact K := by
     apply isCompact_iUnion
     intro i
     obtain ⟨U,_hU,hKU,hs,_he,_hf⟩ := hf i
     exact (closedBall_isCompact 3 (r i)).image_of_continuousOn (hs.continuousOn.mono hKU)
   have hKT : K⊆T := by
     intro x hx
     obtain ⟨i,y,hy,rfl⟩ := mem_iUnion.mp hx
     exact hinto i hy
   have hdim : Module.finrank ℝ (Ambient 3)=Module.finrank ℝ CubicAmbient := by
     simp [Ambient,CubicAmbient,PlaneBase,Module.finrank_pi_fintype,Complex.finrank_real_complex]
   have hinv (x : CubicAmbient) (hx : x∈K) :
       (outerAmbientForm (A := A) (B := B) L S (D 0*c) t δ x).IsInvertible := by
     obtain ⟨i,y,hy,rfl⟩ := mem_iUnion.mp hx
     exact (hf i).target_invertible hdim hy (successorStandardForm_isInvertible 2)
   obtain ⟨τ,hτ,hτη,hall⟩ := exists_uniform_outer_bubble_transfer hmp hN t δ c hD hD0 hK hinv
     hT hKT hη
   refine ⟨τ,hτ,hτη,?_⟩
   intro ε hε
   obtain ⟨g,W,hW,hKW,hg,he,hgT,hgf⟩ := hall ε hε
   obtain ⟨hcomp,hdj⟩ := postcompose_form_packing (fun i => closedBall 3 (r i))
     (fun _ => successorStandardForm 2)
     (outerAmbientForm (A := A) (B := B) L S (D 0*c) t δ)
     (cubicOuterBubbleForm (A := A) (B := B) L S m p N t δ c D ε)
     hW g hg.contMDiff.contMDiffOn he (by
       intro x hx v w
       simp only [mfderiv_eq_fderiv]
       convert! hgf x hx v w using 1) f hf
     (fun i x hx => hKW (mem_iUnion.mpr ⟨i,x,hx,rfl⟩)) hd
   exact ⟨fun i => g ∘ f i,hcomp,
     fun i x hx => hgT (hKW (mem_iUnion.mpr ⟨i,x,hx,rfl⟩)),hdj⟩

 def firstToDistinguished (z : CubicAmbient) : Fin 3 → ℂ :=
   ![z.2⁻¹,z.1.1/z.2,z.1.2/z.2]

 def distinguishedToFirst (z : Fin 3 → ℂ) : CubicAmbient :=
   ((z 1/z 0,z 2/z 0),(z 0)⁻¹)

 theorem firstToDistinguished_smoothAt {z : CubicAmbient} (hz : z.2≠0) :
     ContDiffAt ℝ ∞ firstToDistinguished z := by
   have hC : ContDiffAt ℂ ∞ firstToDistinguished z := by
     apply contDiffAt_pi.mpr
     intro i
     fin_cases i
     · exact contDiffAt_snd.inv hz
     · exact contDiffAt_fst.fst.div contDiffAt_snd hz
     · exact contDiffAt_fst.snd.div contDiffAt_snd hz
   exact hC.restrict_scalars ℝ

 theorem distinguishedToFirst_smoothAt {z : Fin 3 → ℂ} (hz : z 0≠0) :
     ContDiffAt ℝ ∞ distinguishedToFirst z := by
   have h (i : Fin 3) : ContDiffAt ℂ ∞ (fun y : Fin 3 → ℂ => y i) z :=
     (contDiff_apply ℂ ℂ i).contDiffAt
   have hC : ContDiffAt ℂ ∞ distinguishedToFirst z :=
     ((h 1 |>.div (h 0) hz).prodMk (h 2 |>.div (h 0) hz)).prodMk ((h 0).inv hz)
   exact hC.restrict_scalars ℝ

 theorem distinguishedToFirst_first {z : CubicAmbient} (hz : z.2≠0) :
     distinguishedToFirst (firstToDistinguished z)=z := by
   rcases z with ⟨⟨u,v⟩,w⟩
   change ((u/w/w⁻¹,v/w/w⁻¹),w⁻¹⁻¹)=((u,v),w)
   simp [div_inv_eq_mul,hz]

 theorem firstToDistinguished_first {z : Fin 3 → ℂ} (hz : z 0≠0) :
     firstToDistinguished (distinguishedToFirst z)=z := by
   ext i
   fin_cases i <;> simp [firstToDistinguished,distinguishedToFirst,div_inv_eq_mul,hz]

 def firstDistinguishedHomeomorph :
     {z : CubicAmbient // z.2≠0} ≃ₜ {z : Fin 3 → ℂ // z 0≠0} where
   toFun z := ⟨firstToDistinguished z.val,inv_ne_zero z.property⟩
   invFun z := ⟨distinguishedToFirst z.val,inv_ne_zero z.property⟩
   left_inv z := Subtype.ext (distinguishedToFirst_first z.property)
   right_inv z := Subtype.ext (firstToDistinguished_first z.property)
   continuous_toFun := by
     apply Continuous.subtype_mk
     apply continuous_iff_continuousAt.mpr
     intro z
     exact (firstToDistinguished_smoothAt z.property).continuousAt.comp continuous_subtype_val.continuousAt
   continuous_invFun := by
     apply Continuous.subtype_mk
     apply continuous_iff_continuousAt.mpr
     intro z
     exact (distinguishedToFirst_smoothAt z.property).continuousAt.comp continuous_subtype_val.continuousAt

 theorem firstToDistinguished_isEmbedding :
     Topology.IsEmbedding (fun z : {z : CubicAmbient // z.2≠0} => firstToDistinguished z.val) :=
   Topology.IsEmbedding.subtypeVal.comp firstDistinguishedHomeomorph.isEmbedding

 theorem firstToDistinguished_lift {z : CubicAmbient} (hz : z.2≠0) :
     complexAffineLift (firstToDistinguished z)=z.2⁻¹•firstBubbleLift z := by
   ext i
   rcases i with (_|i)
   · simp [complexAffineLift,firstBubbleLift,Pi.smul_apply,smul_eq_mul,hz]
   · fin_cases i <;> simp [complexAffineLift,firstBubbleLift,firstToDistinguished,
       Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,mul_comm]

 theorem firstToDistinguished_lift_near {z : CubicAmbient} (hz : z.2≠0) :
     (fun y => complexAffineLift (firstToDistinguished y))=ᶠ[𝓝 z]
       (fun y : CubicAmbient => y.2⁻¹•firstBubbleLift y) := by
   filter_upwards [(isOpen_ne_fun continuous_snd continuous_const).mem_nhds hz] with y hy
   exact firstToDistinguished_lift hy

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.Hamiltonian
open scoped ContDiff Topology
open Filter

variable {ι κ : Type*} [Fintype ι] [Fintype κ]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

 theorem hopfCurvaturePullback_congr_near {F G : E → (ι → ℂ)} {x : E}
     (h : F=ᶠ[𝓝 x]G) (c : ℝ) (v w : E) :
     hopfCurvaturePullback c F x v w=hopfCurvaturePullback c G x v w := by
   have hc : (fun y => complexCartesian (F y))=ᶠ[𝓝 x](fun y => complexCartesian (G y)) :=
     h.fun_comp complexCartesian
   unfold hopfCurvaturePullback
   rw [h.eq_of_nhds,hc.fderiv_eq]

 theorem degreeHopfCurvaturePullback_congr_near {P : (ι → ℂ) → (κ → ℂ)}
     {F G : E → (ι → ℂ)} {x : E} (h : F=ᶠ[𝓝 x]G) (q c d : ℝ) (v w : E) :
     degreeHopfCurvaturePullback q P c d F x v w=degreeHopfCurvaturePullback q P c d G x v w := by
   unfold degreeHopfCurvaturePullback
   rw [hopfCurvaturePullback_congr_near h]
   exact congrArg (fun u : ℝ => (1-q*d)*hopfCurvaturePullback c G x v w+d*u)
     (hopfCurvaturePullback_congr_near (h.fun_comp P) c v w)

 theorem homogeneousMixedPrimitive_exterior {P : (ι → ℂ) → (κ → ℂ)}
     (hP : ContDiff ℝ ∞ P) {F : E → (ι → ℂ)} (hF : ContDiff ℝ ∞ F)
     {x : E} (hx : complexCartesian (F x)≠0) (hPx : complexCartesian (P (F x))≠0)
     (q c d : ℝ) (v w : E) :
     euclideanExteriorOneForm ((1-q*d)•primitivePullback (hopfPrimitive c) (complexCartesian ∘ F)+
       d•primitivePullback (hopfPrimitive c) (complexCartesian ∘ P ∘ F)) x v w=
       degreeHopfCurvaturePullback q P c d F x v w := by
   have hFC := complexCartesian.contDiff.comp hF
   have hPC := complexCartesian.contDiff.comp (hP.comp hF)
   have hα := primitivePullback_smoothAt (g := complexCartesian ∘ F) (hopfPrimitive_smoothAt c hx) hFC.contDiffAt
   have hβ := primitivePullback_smoothAt (g := complexCartesian ∘ P ∘ F) (hopfPrimitive_smoothAt c hPx) hPC.contDiffAt
   erw [euclideanExteriorOneForm_add ((hα.differentiableAt (by simp)).const_smul (1-q*d))
       ((hβ.differentiableAt (by simp)).const_smul d),
     euclideanExteriorOneForm_smul (1-q*d) (hα.differentiableAt (by simp)),
     euclideanExteriorOneForm_smul d (hβ.differentiableAt (by simp)),
     primitivePullback_exteriorAt (g := complexCartesian ∘ F) (hopfPrimitive_smoothAt c hx) hFC.contDiffAt,
     primitivePullback_exteriorAt (g := complexCartesian ∘ P ∘ F) (hopfPrimitive_smoothAt c hPx) hPC.contDiffAt]
   rfl

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Topology
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment FiniteMoment.Radial

 theorem cubicOuterBubbleForm_homogeneous {A B : ℕ} (L S m p N : ℕ) (t δ c : ℝ)
     (D : ℝ → ℝ) (ε : ℝ) (z v w : CubicAmbient) :
     cubicOuterBubbleForm (A := A) (B := B) L S m p N t δ c D ε z v w=
       degreeHopfCurvaturePullback (L:ℝ)
         (cubicBubblePolynomial (A := A) (B := B) L S m p N t δ ε) c (D ε) firstBubbleLift z v w := by
   have hzn : complexCartesian (firstBubbleLift z)≠0 := by
     intro h
     exact firstBubbleLift_nonzero z (complexCartesian.injective (h.trans (map_zero _).symm))
   exact homogeneousMixedPrimitive_exterior (cubicBubblePolynomial_real_smooth t δ ε)
     (firstBubbleLift_smooth.restrict_scalars ℝ) hzn
       (cubicOuterBubble_nonzero L S m p N t δ ε z) (L:ℝ) c (D ε) v w

 theorem firstToDistinguished_curvature {L S A B m p N : ℕ}
     (hAS : A<S) (hS : 2*S<L) (hB : 3*B<L+S) (hm : m≤L) (t δ c : ℝ)
     (D : ℝ → ℝ) {ε : ℝ} (hε : ε≠0) {z : CubicAmbient} (hz : z.2≠0) (v w : CubicAmbient) :
     degreeAffineForm (L:ℝ) (cubicBubblePolynomial (A := A) (B := B) L S m p N t δ ε) c (D ε)
       (firstToDistinguished z) (fderiv ℝ firstToDistinguished z v) (fderiv ℝ firstToDistinguished z w)=
       cubicOuterBubbleForm (A := A) (B := B) L S m p N t δ c D ε z v w := by
   have hP := cubicBubblePolynomial_real_smooth (L := L) (S := S) (A := A) (B := B) (m := m) (p := p) (N := N) t δ ε
   rw [degreeAffineForm_pullback hP ((firstToDistinguished_smoothAt hz).differentiableAt (by simp)),
     cubicOuterBubbleForm_homogeneous]
   have hlocal := degreeHopfCurvaturePullback_congr_near
     (P := cubicBubblePolynomial (A := A) (B := B) L S m p N t δ ε)
     (firstToDistinguished_lift_near hz) (L:ℝ) c (D ε) v w
   exact hlocal.trans (degreeHopfCurvaturePullback_gauge hP
     (fun x hx => cubicBubblePolynomial_nonzero L S m p N t δ (Complex.ofReal_ne_zero.mpr hε) hx)
     (cubicBubblePolynomial_homogeneous hAS hS hB hm p N t δ ε)
     ((differentiableAt_snd (𝕜 := ℝ)).inv hz)
     ((firstBubbleLift_smooth.restrict_scalars ℝ).differentiable (by simp) z)
     (inv_ne_zero hz) (firstBubbleLift_nonzero z) c (D ε) v w)

end PackingSufficiencySupport.CubicModel
end

end OAI
