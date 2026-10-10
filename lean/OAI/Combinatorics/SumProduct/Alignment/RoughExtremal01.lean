import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RoughDimension01
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

section
section
noncomputable section
end
 
end

section
 

 

noncomputable section
namespace RoughExtremalProgressions
open Finset

 
def APFree (H : ℕ) (A : Finset ℕ) : Prop :=
  ∀ a b : ℕ,0<b → ¬∀ j : Fin (H+1),a+b*j.val∈A

 
def extremal (H K : ℕ) : ℕ := by
  classical
  exact ((range K).powerset.filter (APFree H)).sup card

lemma le_extremal {H K : ℕ} {A : Finset ℕ} (hA : A⊆range K) (hf : APFree H A) :
    A.card≤extremal H K:=by
  classical
  exact le_sup (f:=card) (mem_filter.mpr ⟨mem_powerset.mpr hA,hf⟩)

lemma extremal_le (H K : ℕ) : extremal H K≤K:=by
  classical
  apply Finset.sup_le
  intro A hA
  have h:=card_le_card (mem_powerset.mp (mem_filter.mp hA).1)
  simpa only [card_range] using h

 
def blockResidues (A : Finset ℕ) (K q : ℕ) : Finset ℕ :=
  (A.filter (fun i=>i/K=q)).image (fun i=>i%K)

lemma blockResidues_subset (A : Finset ℕ) {K : ℕ} (hK : 0<K) (q : ℕ) :
    blockResidues A K q⊆range K:=by
  intro a ha
  obtain ⟨i,hi,rfl⟩:=mem_image.mp ha
  exact mem_range.mpr (Nat.mod_lt _ hK)

lemma blockResidues_card (A : Finset ℕ) (K q : ℕ) :
    (blockResidues A K q).card=(A.filter (fun i=>i/K=q)).card:=by
  classical
  apply card_image_iff.mpr
  intro i hi j hj he
  have hiq: i/K=q:=(mem_filter.mp hi).2
  have hjq: j/K=q:=(mem_filter.mp hj).2
  have hh:=Nat.mod_add_div i K
  have hh':=Nat.mod_add_div j K
  change i%K=j%K at he
  rw [hiq] at hh
  rw [hjq] at hh'
  omega

lemma mem_from_residue {A : Finset ℕ} {K q a : ℕ}
    (ha : a∈blockResidues A K q) : q*K+a∈A:=by
  obtain ⟨i,hi,he⟩:=mem_image.mp ha
  obtain ⟨hiA,hiq⟩:=mem_filter.mp hi
  have hx : q*K+a=i:=by nlinarith [Nat.mod_add_div i K]
  rwa [hx]

 
lemma block_APFree {A : Finset ℕ} {H K : ℕ} (hH : 0<H) (hK : 0<K)
    (hno : ∀ a b : ℕ,0<b →b≤K → ¬∀ j : Fin (H+1),a+b*j.val∈A) (q : ℕ) :
    APFree H (blockResidues A K q):=by
  intro a b hb hj
  have h1:=hj ⟨1,by omega⟩
  have hbK : b≤K:=by
    have hx:=mem_range.mp (blockResidues_subset A hK q h1)
    simp only [mul_one] at hx
    omega
  apply hno (q*K+a) b hb hbK
  intro j
  have h:=mem_from_residue (hj j)
  simpa only [Nat.add_assoc] using h

 

theorem card_le_extremal_blocks {A : Finset ℕ} {N H K : ℕ}
    (hA : A⊆range N) (hH : 0<H) (hK : 0<K)
    (hno : ∀ a b : ℕ,0<b →b≤K → ¬∀ j : Fin (H+1),a+b*j.val∈A) :
    A.card≤(N/K+1)*extremal H K:=by
  classical
  have hfiber : ∀ q : ℕ,(A.filter (fun i=>i/K=q)).card≤extremal H K:=by
    intro q
    rw [←blockResidues_card]
    exact le_extremal (blockResidues_subset A hK q) (block_APFree hH hK hno q)
  have hsum : (∑ q∈range (N/K+1),(A.filter (fun i=>i/K=q)).card)=A.card:=by
    rw [sum_card_fiberwise_eq_card_filter]
    congr 1
    apply filter_eq_self.mpr
    intro i hi
    apply mem_range.mpr
    have hiN:=mem_range.mp (hA hi)
    exact Nat.lt_succ_of_le (Nat.div_le_div_right hiN.le)
  rw [←hsum]
  calc
    _≤∑ q∈range (N/K+1),extremal H K:=sum_le_sum (fun q _=>hfiber q)
    _= _:=by simp

 

theorem density_le_extremal {A : Finset ℕ} {N H K : ℕ}
    (hA : A⊆range N) (hN : 0<N) (hH : 0<H) (hK : 0<K)
    (hno : ∀ a b : ℕ,0<b →b≤K → ¬∀ j : Fin (H+1),a+b*j.val∈A) :
    (A.card:ℝ)/N≤(extremal H K:ℝ)/K+(K:ℝ)/N:=by
  have hN' : 0<(N:ℝ):=by exact_mod_cast hN
  have hK' : 0<(K:ℝ):=by exact_mod_cast hK
  have hc : (A.card:ℝ)≤((N/K:ℕ)+1:ℕ)*(extremal H K:ℝ):=by
    exact_mod_cast card_le_extremal_blocks hA hH hK hno
  have hd : ((N/K:ℕ):ℝ)*(K:ℝ)≤N:=by exact_mod_cast Nat.div_mul_le_self N K
  have he : (extremal H K:ℝ)≤K:=by exact_mod_cast extremal_le H K
  have he0 : 0≤(extremal H K:ℝ):=by positivity
  rw [div_le_iff₀ hN']
  have hdc : ((N/K:ℕ):ℝ)*(extremal H K:ℝ)≤(N:ℝ)/K*(extremal H K:ℝ):=by
    exact mul_le_mul_of_nonneg_right ((le_div_iff₀ hK').mpr hd) he0
  push_cast at hc
  have eqn : ((extremal H K:ℝ)/K+(K:ℝ)/N)*(N:ℝ)=
      (N:ℝ)/K*(extremal H K:ℝ)+(K:ℝ):=by field_simp
  rw [eqn]
  nlinarith

end RoughExtremalProgressions

end
 
end

section
 

 

noncomputable section
namespace RoughProgressionDensity
open RationalLattice MalcevCharacters RealPolynomialDegree RoughBadBlock
open FinitePieceAverages RoughSamplingWeights RoughScales Filter
open RoughExtremalProgressions
variable {G : Type} [Group G] [TopologicalSpace G] {r : ℕ}
variable (c : RealCoordinates G r) (Γ : Subgroup G) [mtr : MetricSpace (G⧸Γ)]
local instance : TopologicalSpace (G⧸Γ):=mtr.toUniformSpace.toTopologicalSpace

 

def BadAt (v : ℕ) (c₀ C₀ : ℝ) (B : NNReal) (η Z : ℝ)
    (P : (Fin (v+1)→ℝ)→G) (t : ℤ) : Prop :=
  ∃ (lo hi : Fin v→ℝ) (res : Fin v→ℤ) (test : (G⧸Γ)→ℂ),
    (∀ i,c₀*Z≤hi i-lo i) ∧ (∀ i,-C₀*Z≤lo i ∧ hi i≤C₀*Z) ∧
    LipschitzWith B test ∧ (∀ y,‖test y‖≤B) ∧
    η≤‖mean (boxIndices lo hi (fun _=>0) 1)
      (fun x=>test (QuotientGroup.mk (P (Fin.cons (t:ℝ) (fun i=>(x i:ℝ))))))-
    mean (physicalResidueBox lo hi res t.natAbs)
      (fun x=>test (QuotientGroup.mk (P (Fin.cons (t:ℝ) (fun i=>(x i:ℝ))))))‖

 

def blockOfProgression {v D H w : ℕ} {c₀ C₀ : ℝ} {B : NNReal} {η S Z : ℝ}
    (P : (Fin (v+1)→ℝ)→G) (hP : ∀ i,HasDegree (fun y=>canonicalLog c (P y) i) D)
    (a m : ℤ) (hm : 0 < m) (hsm : Smooth w m)
    (hrange : ∀ z : ℤ,0≤z →z≤H →S≤((a+m*z:ℤ):ℝ) ∧ ((a+m*z:ℤ):ℝ)<2*S)
    (hrough : ∀ z : ℤ,0≤z →z≤H →Rough w (a+m*z))
    (hbad : ∀ j : Fin (H+1),BadAt Γ v c₀ C₀ B η Z P (a+m*(j.val:ℤ))) :
    Block c Γ v D c₀ C₀ B η w S Z H:=by
  classical
  choose lo hi res test hside hbox hlip hbound hdisc using hbad
  refine {
    start:=a, step:=m, positive:=hm, smooth:=hsm, scales:=hrange, rough:=hrough,
    P:=fun y=>P (Fin.cons ((a:ℝ)+(m:ℝ)*y 0) (Fin.tail y)),
    degree:=fun i=>RoughPolynomialDegree.time_affine (hP i) _ _,
    lo:=lo, hi:=hi, res:=res, test:=test,
    side:=hside, box:=hbox, lip:=hlip, bound:=hbound, bad:=?_ }
  intro j
  simpa only [Fin.cons_zero,Fin.tail_cons,Int.cast_add,Int.cast_mul,Int.cast_natCast]
    using hdisc j

lemma rough_add_multiple {w : ℕ} {a L : ℤ} (ha : Rough w a)
    (hL : (primorial w:ℤ)∣L) (z : ℤ) : Rough w (a+L*z):=by
  intro p hp hpw hdiv
  have hpW : (p:ℤ)∣(primorial w:ℤ):=Int.natCast_dvd.mpr (hp.dvd_primorial_iff.mpr hpw)
  have hpL : (p:ℤ)∣L:=hpW.trans hL
  apply ha p hp hpw
  have h:=dvd_sub hdiv (dvd_mul_of_dvd_left hpL z)
  simpa using h

 

def badIndices (v N : ℕ) (c₀ C₀ : ℝ) (B : NNReal) (η Z : ℝ)
    (P : (Fin (v+1)→ℝ)→G) (a L : ℤ) : Finset ℕ:=by
  classical
  exact (Finset.range N).filter (fun i=>BadAt Γ v c₀ C₀ B η Z P (a+L*(i:ℤ)))

omit [TopologicalSpace G] in
lemma mem_badIndices {v N : ℕ} {c₀ C₀ : ℝ} {B : NNReal} {η Z : ℝ}
    {P : (Fin (v+1)→ℝ)→G} {a L : ℤ} {i : ℕ} :
    i∈badIndices Γ v N c₀ C₀ B η Z P a L ↔
      i<N ∧ BadAt Γ v c₀ C₀ B η Z P (a+L*(i:ℤ)):=by
  classical
  simp [badIndices]

 

lemma no_bounded_AP {v D H w N K : ℕ} {c₀ C₀ : ℝ} {B : NNReal} {η S Z : ℝ}
    (hno : IsEmpty (Block c Γ v D c₀ C₀ B η w S Z H)) (hK : K≤w)
    (P : (Fin (v+1)→ℝ)→G) (hP : ∀ i,HasDegree (fun y=>canonicalLog c (P y) i) D)
    (a L : ℤ) (hL : 0<L) (hsm : Smooth w L) (hWL : (primorial w:ℤ)∣L)
    (ha : Rough w a)
    (hscale : ∀ i : ℕ,i<N →S≤((a+L*(i:ℤ):ℤ):ℝ) ∧ ((a+L*(i:ℤ):ℤ):ℝ)<2*S) :
    ∀ u b : ℕ,0<b →b≤K → ¬∀ j : Fin (H+1),u+b*j.val∈badIndices Γ v N c₀ C₀ B η Z P a L:=by
  intro u b hb hbK hap
  have hbs : Smooth w (b:ℤ):=smooth_of_abs_le (by exact_mod_cast hb.ne') (by simpa using hbK.trans hK)
  have hs : Smooth w (L*(b:ℤ)):=RoughRationalBlock.smooth_mul hsm hbs
  have hbad : ∀ j : Fin (H+1),
      BadAt Γ v c₀ C₀ B η Z P (a+L*(u:ℤ)+(L*(b:ℤ))*(j.val:ℤ)):=by
    intro j
    have he : a+L*(u:ℤ)+(L*(b:ℤ))*(j.val:ℤ)=a+L*((u+b*j.val:ℕ):ℤ):=by push_cast; ring
    rw [he]
    exact ((mem_badIndices Γ).mp (hap j)).2
  have hrange : ∀ z : ℤ,0≤z →z≤H →
      S≤((a+L*(u:ℤ)+(L*(b:ℤ))*z:ℤ):ℝ) ∧ ((a+L*(u:ℤ)+(L*(b:ℤ))*z:ℤ):ℝ)<2*S:=by
    intro z hz hzH
    let j : Fin (H+1):=⟨z.toNat,by omega⟩
    have he : a+L*(u:ℤ)+(L*(b:ℤ))*z=a+L*((u+b*j.val:ℕ):ℤ):=by
      simp only [j,Nat.cast_add,Nat.cast_mul,Int.toNat_of_nonneg hz]
      ring
    rw [he]
    exact hscale _ ((mem_badIndices Γ).mp (hap j)).1
  have hr : ∀ z : ℤ,0≤z →z≤H →Rough w (a+L*(u:ℤ)+(L*(b:ℤ))*z):=by
    intro z _ _
    have he : a+L*(u:ℤ)+(L*(b:ℤ))*z=a+L*((u:ℤ)+(b:ℤ)*z):=by ring
    rw [he]
    exact rough_add_multiple ha hWL _
  exact hno.false (blockOfProgression c Γ P hP _ _ (mul_pos hL (by exact_mod_cast hb)) hs hrange hr hbad)

variable [IsTopologicalGroup G] (hsk : SecondKind c)
variable (hΓ : ∀ g : G,g∈Γ ↔ ∀ i,∃ z : ℤ,c.coord g i=z)
variable (htop : mtr.toUniformSpace.toTopologicalSpace=QuotientGroup.instTopologicalSpace Γ)

include hsk hΓ htop in
 

theorem eventual_density_bound (v D : ℕ) (c₀ C₀ : ℝ) (B : NNReal) (η : ℝ)
    (hc₀ : 0<c₀) (hC₀ : 0<C₀) (hB : 0<B) (hη : 0<η)
    (w : ℕ→ℕ) (S Z : ℕ→ℝ) (hw : Tendsto w atTop atTop) (hS : Tendsto S atTop atTop)
    (hZ : ∀ k : ℕ,Tendsto (fun n=>Z n/S n^k) atTop atTop) :
    ∃ H : ℕ,0<H ∧ ∀ K : ℕ,0<K →∀ᶠ n in atTop,
      ∀ (N : ℕ),0<N →∀ (a L : ℤ),0<L →Smooth (w n) L →(primorial (w n):ℤ)∣L →
      Rough (w n) a →
      (∀ i : ℕ,i<N →S n≤((a+L*(i:ℤ):ℤ):ℝ) ∧ ((a+L*(i:ℤ):ℤ):ℝ)<2*S n) →
      ∀ P : (Fin (v+1)→ℝ)→G,(∀ i,HasDegree (fun y=>canonicalLog c (P y) i) D) →
      ((badIndices Γ v N c₀ C₀ B η (Z n) P a L).card:ℝ)/N≤
        (extremal H K:ℝ)/K+(K:ℝ)/N:=by
  classical
  obtain ⟨H,hH,hno⟩:=RoughDimensionInduction.no_long_blocks r G c hsk Γ hΓ mtr htop
    v D c₀ C₀ B η hc₀ hC₀ hB hη w S Z hw hS hZ
  refine ⟨H,hH,fun K hK=>?_⟩
  filter_upwards [hno,hw.eventually (eventually_ge_atTop K)] with n hnoN hwK
  intro N hN a L hL hsm hWL ha hscale P hP
  exact density_le_extremal (Finset.filter_subset _ _) hN hH hK
    (no_bounded_AP c Γ hnoN hwK P hP a L hL hsm hWL ha hscale)

end RoughProgressionDensity

end
end
end

end OAI
