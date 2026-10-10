import Mathlib
import OAI.Geometry.BallPacking.Models.CubicPhysicalLocality

namespace OAI

noncomputable section

namespace PackingSufficiencySupport
open scoped BigOperators Pointwise
open MeasureTheory Set
open MomentPolytope

theorem exists_six_model_comparison_data {ι : Type*} [Fintype ι] [Nonempty ι]
    (r : ι → ℝ) (hr : ∀ i,0 < r i) {a : ℝ} (ha : 1/2<a) (_ha1 : a<1)
    (hrs : ∀ i,r i<1-a) (hvol : ∑ i,r i^3<1-a^3) :
    ∃ h₁ c d₁ h₂ d₂ : ℚ, ∃ τ ε : ℝ,
      (∀ i,r i<h₁) ∧ h₁<c ∧ (c:ℝ)<1-a ∧ 1-a<(d₁:ℝ) ∧ d₁<h₂ ∧
      h₂<d₂ ∧ (d₂:ℝ)<(2-a)/3 ∧ 0<(h₁:ℝ) ∧ 0<(h₂:ℝ) ∧
      0<τ ∧ τ<1 ∧ 0<ε ∧
      (∀ i,momentSimplex 2 (r i) ⊆ τ • region sixModelBounds ![h₁,h₂]) ∧
      ConcaveOn ℝ (region sixModelBounds ![h₁,h₂]) (sixModelGap (1-a) ((2-a)/3) r) ∧
      (0 < ∫ p in region sixModelBounds ![h₁,h₂],sixModelGap (1-a) ((2-a)/3) r p) ∧
      ∀ p ∈ region sixModelBounds ![h₁,h₂], p ∉ τ • region sixModelBounds ![h₁,h₂] →
        ε ≤ sixModelGap (1-a) ((2-a)/3) r p := by
  classical
  let S := Finset.univ.image r
  have hS : S.Nonempty := Finset.image_nonempty.2 Finset.univ_nonempty
  let R := S.max' hS
  have hR (i : ι) : r i ≤ R := Finset.le_max' S (r i) (Finset.mem_image_of_mem r (Finset.mem_univ i))
  have hRs : R<1-a := (Finset.max'_lt_iff S hS).2 (by
    intro x hx
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.1 hx
    exact hrs i)
  have hRpos : 0<R := (hr (Classical.arbitrary ι)).trans_le (hR _)
  have hsb : 1-a<(2-a)/3 := by linarith
  have hlim : (∑ i,r i^3)/6<sixModelMean (1-a) ((2-a)/3) (1-a) ((2-a)/3) := by
    rw [sixModelMean_limit_value]
    exact div_lt_div_of_pos_right hvol (by norm_num)
  obtain ⟨h₁,h₂,c,d₂,hRh₁,hch₁,hcs,hsh₂,hhd₂,hd₂,hmean⟩ :=
    rational_truncation_pair (fun h => sixModelMean (1-a) ((2-a)/3) h.1 h.2)
      (continuous_sixModelMean (1-a) ((2-a)/3)) hRs hsb hlim
  obtain ⟨d₁,hsd₁,hd₁h₂⟩ := exists_rat_btwn hsh₂
  have hd₁h₂' : d₁<h₂ := by exact_mod_cast hd₁h₂
  have hh₁ : (0:ℝ)<h₁ := hRpos.trans hRh₁
  have hRh₂ : R<(h₂:ℝ) := hRs.trans hsh₂
  have hh₂ : (0:ℝ)<h₂ := hRpos.trans hRh₂
  have hh₁s : (h₁:ℝ)<1-a := (by exact_mod_cast hch₁ : (h₁:ℝ)<c).trans hcs
  have hh₂b : (h₂:ℝ)<(2-a)/3 := (by exact_mod_cast hhd₂ : (h₂:ℝ)<d₂).trans hd₂
  have hratio : max (R/(h₁:ℝ)) (R/(h₂:ℝ))<1 := max_lt
    ((div_lt_one hh₁).2 hRh₁) ((div_lt_one hh₂).2 hRh₂)
  obtain ⟨τ,hτlo,hτhi⟩ := exists_between hratio
  have hτlo₁ : R/(h₁:ℝ)<τ := (le_max_left _ _).trans_lt hτlo
  have hτlo₂ : R/(h₂:ℝ)<τ := (le_max_right _ _).trans_lt hτlo
  have hτ : 0<τ := (div_pos hRpos hh₁).trans hτlo₁
  have hRτ₁ : R<τ*(h₁:ℝ) := (div_lt_iff₀ hh₁).1 hτlo₁
  have hRτ₂ : R<τ*(h₂:ℝ) := (div_lt_iff₀ hh₂).1 hτlo₂
  let ε := 9*((2-a)/3-(h₂:ℝ))
  have hε : 0<ε := mul_pos (by norm_num) (sub_pos.2 hh₂b)
  have hcap (i : ι) : momentSimplex 2 (r i) ⊆ τ • region sixModelBounds ![h₁,h₂] := by
    apply cap_into_scaled_region _ _ sixModelBounds_le_one hτ
    intro ν
    fin_cases ν
    · exact (hR i).trans hRτ₁.le
    · exact (hR i).trans hRτ₂.le
  refine ⟨h₁,c,d₁,h₂,d₂,τ,ε,fun i => (hR i).trans_lt hRh₁,hch₁,hcs,hsd₁,hd₁h₂',
    hhd₂,hd₂,hh₁,hh₂,hτ,hτhi,hε,hcap,?_,?_,?_⟩
  · rw [sixModelGap_eq_cappedAffine]
    apply concaveOn_cappedAffine _ _ _ _ ?_ (convex_region _ _)
    intro i
    cases i <;> norm_num
  · rw [integral_sixModelGap r (fun i => (hr i).le) hh₁.le hh₁s.le hsh₂.le
      (fun i => (hR i).trans hRh₁.le) (fun i => (hR i).trans hRh₂.le)]
    linarith
  · intro p hp hout
    have hz := sum_caps_zero_outside r (fun _ hp => hp.1) hcap hp hout
    simp only [sixModelGap,hz,sub_zero]
    exact sixModelDensity_lower hsh₂.le hp

end PackingSufficiencySupport

namespace PackingSufficiencySupport.CubicModel
open scoped ContDiff Manifold Topology BigOperators Pointwise
open Set Function Filter Manifold MeasureTheory
open DiagonalQuadrics DiagonalQuadrics.Explicit Hamiltonian FiniteMoment MomentPolytope

 theorem actual_six_cubic_inner_normal_packing_large (Q : ℕ) {N : ℕ} [Nonempty (Fin N)]
    (r r' : Fin N → ℝ) (hr : ∀ i,0<r i) (hr' : ∀ i,0≤r' i)
    (hrr : ∀ i,r' i<r i) {a : ℚ} (ha : (1:ℚ)/2<a) (ha1 : a<1)
    (hrs : ∀ i,r i<1-(a:ℝ)) (hvol : ∑ i,r i^3<1-(a:ℝ)^3) :
    ∃ L A B D S : ℕ,Q<L ∧ 0<L ∧ 0<A ∧ 0<S ∧ A<S ∧ A≤B ∧ S≤B ∧ 3*B<D ∧ 3*S<D ∧
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
  obtain ⟨L,A,B,D,S,hQL,hL,hA,hS0,hAS,hAB,hSB,hB,hS,heA,heB,heD,heS⟩ :=
    exists_six_cubic_inner_weights_large Q ha ha1
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
  refine ⟨L,A,B,D,S,hQL,hL,hA,hS0,hAS,hAB,hSB,hB,hS,heD,heS,h₁,h₂,hrh,hh₁₂,?_,?_,ℓ,φ,?_,hm,hd⟩
  · rw [heA,mul_div_cancel_left₀ _ hLr.ne']
    exact_mod_cast hhe
  · rw [heB,mul_div_cancel_left₀ _ hLr.ne']
    exact hh₂d
  · intro i
    exact (hφ i).congr_target_near (fun x hx => interior_subset (hm i hx))
      (physicalCoupling_representative_near hLr.le hPS he)

end PackingSufficiencySupport.CubicModel

namespace PackingSufficiencySupport.Hamiltonian
open scoped BigOperators ContDiff ComplexConjugate
open DiagonalQuadrics

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def complexBlocks (s : ι → ℂ) (z : ι → κ → ℂ) : ι × κ → ℂ := fun ij => s ij.1*z ij.1 ij.2

theorem complexArea_add (z u v : ℂ) : complexArea z (u+v)=complexArea z u+complexArea z v := by
  simp only [complexArea,mul_add,Complex.add_im]

theorem complexArea_product (s t u v : ℂ) :
    complexArea (s*t) (u*t+s*v)=Complex.normSq t*complexArea s u+Complex.normSq s*complexArea t v := by
  rw [complexArea_add,mul_comm u t,mul_comm s t,complexArea_mul,mul_comm t s,complexArea_mul]

theorem complexBlocks_sq (s : ι → ℂ) (z : ι → κ → ℂ) :
    phaseSq (complexCartesian (complexBlocks s z))=
      ∑ i,Complex.normSq (s i)*phaseSq (complexCartesian (z i)) := by
  simp only [complexCartesian_sq,complexBlocks,Fintype.sum_prod_type,Complex.normSq_mul,Finset.mul_sum]

theorem complexBlocks_area (s d : ι → ℂ) (z v : ι → κ → ℂ) :
    phaseArea (complexCartesian (complexBlocks s z))
      (complexCartesian (fun ij => d ij.1*z ij.1 ij.2+s ij.1*v ij.1 ij.2))=
    ∑ i,(phaseSq (complexCartesian (z i))*complexArea (s i) (d i)+
      Complex.normSq (s i)*phaseArea (complexCartesian (z i)) (complexCartesian (v i))) := by
  have he (a b : κ → ℂ) : phaseArea (complexCartesian a) (complexCartesian b)=
      ∑ j,complexArea (a j) (b j) := by
    simp only [←complexPairing_im,complexPairing,Complex.im_sum,Complex.star_def,complexArea]
  rw [show phaseArea (complexCartesian (complexBlocks s z))
      (complexCartesian (fun ij => d ij.1*z ij.1 ij.2+s ij.1*v ij.1 ij.2))=
      ∑ ij : ι × κ,complexArea (s ij.1*z ij.1 ij.2) (d ij.1*z ij.1 ij.2+s ij.1*v ij.1 ij.2) from by
    simp only [←complexPairing_im,complexPairing,Complex.im_sum,Complex.star_def,complexArea,complexBlocks]]
  simp only [Fintype.sum_prod_type,complexArea_product,Finset.sum_add_distrib,←Finset.sum_mul,
    ←Finset.mul_sum,complexCartesian_sq,he]

theorem hopfPrimitive_complexBlocks (s d : ι → ℂ) (z v : ι → κ → ℂ)
    (hz : ∀ i,complexCartesian (z i)≠0) (c : ℝ) :
    hopfPrimitive c (complexCartesian (complexBlocks s z))
      (complexCartesian (fun ij => d ij.1*z ij.1 ij.2+s ij.1*v ij.1 ij.2))=
    (∑ i,(Complex.normSq (s i)*phaseSq (complexCartesian (z i)) /
      phaseSq (complexCartesian (complexBlocks s z)))*
        hopfPrimitive c (complexCartesian (z i)) (complexCartesian (v i)))+
    c/(2*phaseSq (complexCartesian (complexBlocks s z)))*
      ∑ i,phaseSq (complexCartesian (z i))*complexArea (s i) (d i) := by
  simp only [hopfPrimitive,smul_apply,smul_eq_mul,complexBlocks_area,Finset.sum_add_distrib,
    mul_add,Finset.mul_sum]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  field_simp [(phaseSq_pos (hz i)).ne']

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
omit [Fintype ι] [Fintype κ] in
theorem complexBlocks_hasFDerivAt {s : E → ι → ℂ} {G : E → ι → κ → ℂ} {x : E}
    (hs : ∀ i,DifferentiableAt ℝ (fun y => s y i) x)
    (hG : ∀ i,DifferentiableAt ℝ (fun y => G y i) x) :
    HasFDerivAt (fun y => complexBlocks (s y) (G y))
      (ContinuousLinearMap.pi fun ij =>
        (fderiv ℝ (fun y => s y ij.1) x).smulRight (G x ij.1 ij.2)+
          s x ij.1 • ((ContinuousLinearMap.proj ij.2).comp (fderiv ℝ (fun y => G y ij.1) x))) x := by
  apply hasFDerivAt_pi.mpr
  intro ij
  have hproj := (hasFDerivAt_pi'.mp (hG ij.1).hasFDerivAt) ij.2
  convert (hs ij.1).hasFDerivAt.smul hproj using 1
  · rfl
  · rw [add_comm]

end PackingSufficiencySupport.Hamiltonian

namespace PackingSufficiencySupport.FiniteMoment.Radial
open scoped BigOperators Topology ContDiff
open Set Filter Function

variable {ι : Type*} [Fintype ι]

abbrev DiskPair := ℂ × ℂ

def squaredRadii (z : DiskPair) : Plane := (Complex.normSq z.1,Complex.normSq z.2)

theorem squaredRadii_nonneg (z : DiskPair) : 0≤(squaredRadii z).1 ∧ 0≤(squaredRadii z).2 :=
  ⟨Complex.normSq_nonneg _,Complex.normSq_nonneg _⟩

theorem squaredRadii_contDiff : ContDiff ℝ ∞ squaredRadii := by
  have hn : ContDiff ℝ ∞ Complex.normSq := by
    change ContDiff ℝ ∞ (fun z : ℂ => z.re*z.re+z.im*z.im)
    exact (Complex.reCLM.contDiff.mul Complex.reCLM.contDiff).add
      (Complex.imCLM.contDiff.mul Complex.imCLM.contDiff)
  exact (hn.comp contDiff_fst).prodMk (hn.comp contDiff_snd)

def diskDomain (A B : ℝ) : Set DiskPair :=
  {z | (squaredRadii z).1<A ∧ (squaredRadii z).1+(squaredRadii z).2<B}

theorem diskDomain_isOpen (A B : ℝ) : IsOpen (diskDomain A B) :=
  (isOpen_lt squaredRadii_contDiff.continuous.fst continuous_const).inter
    (isOpen_lt (squaredRadii_contDiff.continuous.fst.add squaredRadii_contDiff.continuous.snd) continuous_const)

theorem squaredRadii_mem_lower {A B : ℝ} {z : DiskPair} (hz : z∈diskDomain A B) :
    squaredRadii z∈lowerTrapezoid A B :=
  ⟨(squaredRadii_nonneg z).1,hz.1,(squaredRadii_nonneg z).2,hz.2⟩

def diskForward (k : ι → ℕ × ℕ) (a : ι → ℝ) (z : DiskPair) : DiskPair :=
  (Real.sqrt (slope k a (squaredRadii z)).1 • z.1,
   Real.sqrt (slope k a (squaredRadii z)).2 • z.2)

def diskInverse (k : ι → ℕ × ℕ) (a : ι → ℝ) (z : DiskPair) : DiskPair :=
  ((Real.sqrt (slope k a (nonnegativeInverse k a (squaredRadii z))).1)⁻¹ • z.1,
   (Real.sqrt (slope k a (nonnegativeInverse k a (squaredRadii z))).2)⁻¹ • z.2)

theorem normSq_real_smul (s : ℝ) (z : ℂ) : Complex.normSq (s • z)=s^2*Complex.normSq z := by
  change Complex.normSq ((s:ℂ)*z)=_
  rw [Complex.normSq_mul,Complex.normSq_ofReal]
  ring

theorem squaredRadii_forward {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (h0 : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) (z : DiskPair) :
    squaredRadii (diskForward k a z)=moment k a (squaredRadii z) := by
  have hs := slope_pos ha h0 he0 he1 (squaredRadii_nonneg z)
  rw [moment_eq_radius_slope]
  apply Prod.ext
  · change Complex.normSq (_ • z.1)=_
    rw [normSq_real_smul,Real.sq_sqrt hs.1.le]
    exact mul_comm _ _
  · change Complex.normSq (_ • z.2)=_
    rw [normSq_real_smul,Real.sq_sqrt hs.2.le]
    exact mul_comm _ _

theorem squaredRadii_inverse {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (h0 : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {z : DiskPair}
    (hz : ∃ r : Plane,(0≤r.1 ∧ 0≤r.2) ∧ moment k a r=squaredRadii z) :
    squaredRadii (diskInverse k a z)=nonnegativeInverse k a (squaredRadii z) := by
  have hs := slope_pos ha h0 he0 he1 (nonnegativeInverse_nonneg k a (squaredRadii z))
  have hm := nonnegativeInverse_spec hz
  rw [moment_eq_radius_slope] at hm
  apply Prod.ext
  · change Complex.normSq (_ • z.1)=_
    rw [normSq_real_smul,inv_pow,Real.sq_sqrt hs.1.le]
    change (slope k a (nonnegativeInverse k a (squaredRadii z))).1⁻¹*(squaredRadii z).1=_
    rw [←congrArg Prod.fst hm]
    field_simp [hs.1.ne']
  · change Complex.normSq (_ • z.2)=_
    rw [normSq_real_smul,inv_pow,Real.sq_sqrt hs.2.le]
    change (slope k a (nonnegativeInverse k a (squaredRadii z))).2⁻¹*(squaredRadii z).2=_
    rw [←congrArg Prod.snd hm]
    field_simp [hs.2.ne']

theorem diskForward_inverse {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (h0 : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) {z : DiskPair}
    (hz : ∃ r : Plane,(0≤r.1 ∧ 0≤r.2) ∧ moment k a r=squaredRadii z) :
    diskForward k a (diskInverse k a z)=z := by
  have hs := slope_pos ha h0 he0 he1 (nonnegativeInverse_nonneg k a (squaredRadii z))
  rw [diskForward,squaredRadii_inverse ha h0 he0 he1 hz]
  dsimp only [diskInverse]
  apply Prod.ext
  · exact (smul_smul _ _ _).trans (by rw [mul_inv_cancel₀ (Real.sqrt_pos.mpr hs.1).ne',one_smul])
  · exact (smul_smul _ _ _).trans (by rw [mul_inv_cancel₀ (Real.sqrt_pos.mpr hs.2).ne',one_smul])

theorem diskInverse_forward {k : ι → ℕ × ℕ} {a : ι → ℝ}
    (ha : ∀ i,0<a i) (h0 : ∃ i,k i=(0,0))
    (he0 : ∃ i,k i=(1,0)) (he1 : ∃ i,k i=(0,1)) (z : DiskPair) :
    diskInverse k a (diskForward k a z)=z := by
  have hs := slope_pos ha h0 he0 he1 (squaredRadii_nonneg z)
  rw [diskInverse,squaredRadii_forward ha h0 he0 he1,
    nonnegativeInverse_of_moment ha h0 he0 he1 (squaredRadii_nonneg z)]
  dsimp only [diskForward]
  apply Prod.ext
  · exact (smul_smul _ _ _).trans (by rw [inv_mul_cancel₀ (Real.sqrt_pos.mpr hs.1).ne',one_smul])
  · exact (smul_smul _ _ _).trans (by rw [inv_mul_cancel₀ (Real.sqrt_pos.mpr hs.2).ne',one_smul])

end PackingSufficiencySupport.FiniteMoment.Radial

namespace PackingSufficiencySupport.Hamiltonian
open scoped BigOperators ContDiff ComplexConjugate
open DiagonalQuadrics FiniteMoment.Radial

theorem complexArea_real_smul (z v : ℂ) (r : ℝ) :
    complexArea z (r • v)=r*complexArea z v := by
  simp only [complexArea_apply,Complex.smul_re,Complex.smul_im,smul_eq_mul]
  ring

theorem complexArea_power_derivative (z v : ℂ) (n : ℕ) :
    complexArea (z^n) ((n:ℂ)*z^(n-1)*v)=
      (n:ℝ)*Complex.normSq z^(n-1)*complexArea z v := by
  cases n with
  | zero => simp [complexArea]
  | succ n =>
    rw [Nat.succ_sub_one,pow_succ]
    have he : ((n+1:ℕ):ℂ)*z^n*v=((n+1:ℕ):ℝ) • (z^n*v) := by
      simp only [Complex.real_smul,Complex.ofReal_natCast]
      ring
    rw [he,complexArea_real_smul,complexArea_mul,map_pow]
    ring

def complexMonomial (k : ℕ × ℕ) (z : DiskPair) : ℂ := z.1^k.1*z.2^k.2

def complexMonomialDerivative (k : ℕ × ℕ) (z : DiskPair) : DiskPair →L[ℝ] ℂ :=
  ((k.1:ℂ)*z.1^(k.1-1)*z.2^k.2) • (ContinuousLinearMap.fst ℝ ℂ ℂ)+
    (z.1^k.1*(k.2:ℂ)*z.2^(k.2-1)) • (ContinuousLinearMap.snd ℝ ℂ ℂ)

theorem complexMonomial_contDiff (k : ℕ × ℕ) : ContDiff ℝ ∞ (complexMonomial k) :=
  (contDiff_fst.pow k.1).mul (contDiff_snd.pow k.2)

theorem complexMonomial_hasFDerivAt (k : ℕ × ℕ) (z : DiskPair) :
    HasFDerivAt (complexMonomial k) (complexMonomialDerivative k z) z := by
  have h := (((ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt (x := z)).pow k.1).mul
    (((ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt (x := z)).pow k.2)
  convert! h using 1
  apply ContinuousLinearMap.ext
  intro v
  simp [complexMonomialDerivative]
  ring

theorem complexMonomial_normSq (k : ℕ × ℕ) (z : DiskPair) :
    Complex.normSq (complexMonomial k z)=monomial k (squaredRadii z) := by
  simp only [complexMonomial,Complex.normSq_mul,map_pow,monomial,squaredRadii]

theorem complexMonomial_area (k : ℕ × ℕ) (z v : DiskPair) :
    complexArea (complexMonomial k z) (complexMonomialDerivative k z v)=
      (k.1:ℝ)*(squaredRadii z).1^(k.1-1)*(squaredRadii z).2^k.2*complexArea z.1 v.1+
      (k.2:ℝ)*(squaredRadii z).1^k.1*(squaredRadii z).2^(k.2-1)*complexArea z.2 v.2 := by
  have he : complexMonomialDerivative k z v=
      ((k.1:ℂ)*z.1^(k.1-1)*v.1)*z.2^k.2+
      z.1^k.1*((k.2:ℂ)*z.2^(k.2-1)*v.2) := by
    simp only [complexMonomialDerivative,add_apply,
      smul_apply,ContinuousLinearMap.coe_fst',ContinuousLinearMap.coe_snd',smul_eq_mul]
    ring
  rw [he,complexMonomial,complexArea_product,complexArea_power_derivative,complexArea_power_derivative]
  simp only [map_pow,squaredRadii]
  ring

section

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def toricLift (k : ι → ℕ × ℕ) (G : ι → κ → ℂ) (z : DiskPair) : ι × κ → ℂ :=
  complexBlocks (fun i => complexMonomial (k i) z) G

def toricLiftDifferential (k : ι → ℕ × ℕ) (G V : ι → κ → ℂ) (z v : DiskPair) : ι × κ → ℂ :=
  fun ij => complexMonomialDerivative (k ij.1) z v * G ij.1 ij.2 +
    complexMonomial (k ij.1) z * V ij.1 ij.2

theorem toricLift_sq (k : ι → ℕ × ℕ) (G : ι → κ → ℂ) (z : DiskPair) :
    phaseSq (complexCartesian (toricLift k G z))=
      polynomial k (fun i => phaseSq (complexCartesian (G i))) (squaredRadii z) := by
  rw [toricLift,complexBlocks_sq]
  simp only [complexMonomial_normSq,polynomial,mul_comm]

theorem toricLift_primitive (k : ι → ℕ × ℕ) (G V : ι → κ → ℂ)
    (hG : ∀ i,complexCartesian (G i)≠0) (z v : DiskPair) (c : ℝ) :
    hopfPrimitive c (complexCartesian (toricLift k G z))
      (complexCartesian (toricLiftDifferential k G V z v))=
    (∑ i,probability k (fun j => phaseSq (complexCartesian (G j))) (squaredRadii z) i *
      hopfPrimitive c (complexCartesian (G i)) (complexCartesian (V i)))+
    c/2*((slope k (fun j => phaseSq (complexCartesian (G j))) (squaredRadii z)).1*complexArea z.1 v.1+
      (slope k (fun j => phaseSq (complexCartesian (G j))) (squaredRadii z)).2*complexArea z.2 v.2) := by
  rw [show hopfPrimitive c (complexCartesian (toricLift k G z))
      (complexCartesian (toricLiftDifferential k G V z v))=
      hopfPrimitive c (complexCartesian (complexBlocks (fun i => complexMonomial (k i) z) G))
      (complexCartesian (fun ij => complexMonomialDerivative (k ij.1) z v*G ij.1 ij.2+
        complexMonomial (k ij.1) z*V ij.1 ij.2)) from rfl,
    hopfPrimitive_complexBlocks (fun i => complexMonomial (k i) z)
      (fun i => complexMonomialDerivative (k i) z v) G V hG c]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [complexMonomial_normSq,←toricLift,toricLift_sq]
    simp only [probability]
    congr 2
    exact mul_comm _ _
  · rw [←toricLift,toricLift_sq]
    simp only [complexMonomial_area,FiniteMoment.Radial.slope,slopeNumerator,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,
      mul_add,Finset.sum_add_distrib,Finset.mul_sum,Finset.sum_mul]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

end

variable {ι κ X : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem toricLift_contDiff (k : ι → ℕ × ℕ) :
    ContDiff ℝ ∞ (fun q : (ι → κ → ℂ) × DiskPair => toricLift k q.1 q.2) := by
  apply contDiff_pi.mpr
  intro ij
  dsimp only [toricLift,complexBlocks,complexMonomial]
  fun_prop

theorem toricLift_fderiv {k : ι → ℕ × ℕ} {G : X → ι → κ → ℂ} {z : X → DiskPair} {x : X}
    (hG : DifferentiableAt ℝ G x) (hz : DifferentiableAt ℝ z x) (v : X) :
    fderiv ℝ (fun q => toricLift k (G q) (z q)) x v=
      toricLiftDifferential k (G x) (fderiv ℝ G x v) (z x) (fderiv ℝ z x v) := by
  have hs := ((toricLift_contDiff k).differentiable (by simp) (G x,z x)).comp x (hG.prodMk hz)
  funext ij
  have hi := (hasFDerivAt_pi'.mp ((hasFDerivAt_pi'.mp hG.hasFDerivAt) ij.1)) ij.2
  have hm := (complexMonomial_hasFDerivAt (k ij.1) (z x)).comp x hz.hasFDerivAt
  have hh := hm.mul hi
  have he : fderiv ℝ (fun q => toricLift k (G q) (z q) ij) x=
      (ContinuousLinearMap.proj ij).comp (fderiv ℝ (fun q => toricLift k (G q) (z q)) x) :=
    ((hasFDerivAt_pi'.mp hs.hasFDerivAt) ij).fderiv
  have hh' : HasFDerivAt (fun q => toricLift k (G q) (z q) ij)
      (complexMonomial (k ij.1) (z x) • ((ContinuousLinearMap.proj ij.2).comp
         ((ContinuousLinearMap.proj ij.1).comp (fderiv ℝ G x)))+
       G x ij.1 ij.2 • ((complexMonomialDerivative (k ij.1) (z x)).comp (fderiv ℝ z x))) x := by
    convert! hh using 1
  have hv := congrArg (fun L => L v) (he.symm.trans hh'.fderiv)
  simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply,add_apply,smul_apply,
    smul_eq_mul,toricLiftDifferential,mul_comm,add_comm] using hv

theorem toricLift_pullback_primitive {k : ι → ℕ × ℕ} {G : X → ι → κ → ℂ} {z : X → DiskPair} {x : X}
    (hG : DifferentiableAt ℝ G x) (hz : DifferentiableAt ℝ z x)
    (hne : ∀ i,complexCartesian (G x i)≠0) (v : X) (c : ℝ) :
    hopfPrimitive c (complexCartesian (toricLift k (G x) (z x)))
      (complexCartesian (fderiv ℝ (fun q => toricLift k (G q) (z q)) x v))=
    (∑ i,probability k (fun j => phaseSq (complexCartesian (G x j))) (squaredRadii (z x)) i *
      hopfPrimitive c (complexCartesian (G x i)) (complexCartesian (fderiv ℝ G x v i)))+
    c/2*((slope k (fun j => phaseSq (complexCartesian (G x j))) (squaredRadii (z x))).1*
      complexArea (z x).1 (fderiv ℝ z x v).1+
      (slope k (fun j => phaseSq (complexCartesian (G x j))) (squaredRadii (z x))).2*
      complexArea (z x).2 (fderiv ℝ z x v).2) := by
  rw [toricLift_fderiv hG hz]
  exact toricLift_primitive k _ _ hne _ _ c

end PackingSufficiencySupport.Hamiltonian
end

end OAI
