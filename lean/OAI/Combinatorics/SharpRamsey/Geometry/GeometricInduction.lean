import Mathlib
import OAI.Combinatorics.SharpRamsey.Geometry.ProjectionDescription

namespace OAI

section
namespace SharpLogRamsey.GeometricCover
open Finset Real Filter SourceScales Incidence ProjectiveDuality Validation Projection
open scoped Classical Topology
noncomputable section

def Uniform (r : ℕ) (H : ℝ) : Prop :=
  ∀ η : ℝ,0<η → ∀ C : ℝ,1≤C →
  ∀ᶠ σ : ℝ in atTop,∀ (q : ℕ) [Fact q.Prime],3≤q → exp σ=(q:ℝ) →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod q) V] [FiniteDimensional (ZMod q) V],
    Module.finrank (ZMod q) V=r → ∀ D R,Admissible σ η D R →
    ∀ (U : Finset (Projectivization (ZMod q) V))
      (UT : Finset (Projectivization (ZMod q) (Module.Dual (ZMod q) V)))
      (n t : ℕ) (b τ : ℝ),
    0<n → 0<t → n≤U.card → t≤UT.card →
    0≤b → b≤C*scaleKstar σ η D → 0<τ → τ≤C*σ^(-100*beta η) →
    (q:ℝ)^r*exp (-b)≤(n:ℝ)*t → (n:ℝ)*t≤2*(q:ℝ)^r →
    Validated q (scaleP σ η D R) H r U UT n t τ

lemma uniform_four : Uniform 4 7000 := by
  intro η hη C hC
  exact SpatialPublic.validated_cover hη C hC

private def Description {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (q P J : ℝ) (U : Finset (Projectivization K V))
    (UT : Finset (Projectivization K (Module.Dual K V))) (n t : ℕ) (τ : ℝ) : Prop :=
  ∃ F : Finset (Finset (Projectivization K V)),
    (∀ W∈F,W⊆U ∧ (W.card:ℝ)≤n*exp (6*P)) ∧
    (∀ S T,S⊆U → S.card=n → T⊆UT → T.card=t →
      (incidenceCount S T:ℝ)≤τ*(n:ℝ)*t/q →
      ∃ W∈F,(n:ℝ)/100≤(S∩W).card) ∧
    log ((F.card:ℝ)+1)≤J*q*P*(log ((U.card:ℝ)/n)+log ((UT.card:ℝ)/t)+P)

theorem uniform_step (i : ℕ) (H : ℝ) (hH : 0≤H) (ih : Uniform (i+4) H) :
    Uniform (i+5) (16*H+32*(i:ℝ)+3000) := by
  intro η hη C hC
  let C' := 400*C+4
  have hC' : 1≤C' := by dsimp only [C']; linarith
  have hdec : Tendsto (fun σ : ℝ => C*σ^(-100*beta η)) atTop (𝓝 0) := by
    simpa using (tendsto_rpow_neg_atTop (by have := beta_pos hη; positivity : 0<100*beta η)).const_mul C
  filter_upwards [ih η hη C' hC',
    eventually_uniform_L hη (eventually_ge_atTop (1000000:ℝ)),eventually_uniform_R hη 1,
    eventually_training_loss hη C 1 (by linarith) (by norm_num),
    eventually_P_le_linear hη (1/5) (by norm_num),
    hdec.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/1000000)),
    eventually_ge_atTop (1000000000000:ℝ)]
    with σ hs hL hR hbsmall hPσ hτsmall hσ
  intro q _ hq hex V _ _ _ hdim D R had U UT n t b τ hn ht hnu htu hb hbu hτ hτu hplo hphi
  let P := scaleP σ η D R
  have hσ1 : 1≤σ := by linarith
  have hLP : scaleL σ η D≤P := le_mul_of_one_le_right (by linarith [hL D R had]) (hR D R had)
  have hP : 1000000≤P := (hL D R had).trans hLP
  have hbP : b≤P := by
    have hh := hbsmall D R had b 0 hbu (mul_nonneg (by linarith) (rpow_nonneg (by linarith) _))
    simp only [mul_zero,add_zero,one_mul] at hh
    exact hh.trans hLP
  have hbσ : b≤σ/5 := hbP.trans (by dsimp only [P]; linarith [hPσ D R had])
  have hsmall : τ≤1/1000000 := hτu.trans hτsmall.le
  have hq' : (0:ℝ)<q := by exact_mod_cast (by omega : 0<q)
  have hcard : Nat.card (ZMod q)=q := by simp
  have hK : 1 ≤ scaleKstar σ η D := by
    have hbpos := (beta_pos hη).le
    have hD : 1≤D := (one_le_rpow hσ1 hbpos).trans had.D_lower
    exact one_le_mul_of_one_le_of_one_le hD (one_le_rpow hσ1 (by positivity))
  have hlog4 : 0≤log (4:ℝ) := log_nonneg (by norm_num)
  have hlog4up : log (4:ℝ)≤3 := by have hh := log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4); linarith
  have hb' : b+log 4≤C'*scaleKstar σ η D := by dsimp only [C']; nlinarith
  have hτ' : 400*τ≤C'*σ^(-100*beta η) := by
    have hh := mul_le_mul_of_nonneg_left hτu (show (0:ℝ)≤400 by norm_num)
    dsimp only [C']
    nlinarith [rpow_nonneg (by linarith : 0≤σ) (-100*beta η)]
  have hdesc (W : Type) [AddCommGroup W] [Module (ZMod q) W] [FiniteDimensional (ZMod q) W]
      (hdW : Module.finrank (ZMod q) W=i+5)
      (A : Finset (Projectivization (ZMod q) W))
      (B : Finset (Projectivization (ZMod q) (Module.Dual (ZMod q) W)))
      (a c : ℕ) (ha : 0<a) (hc : 0<c) (haA : a≤A.card) (hcB : c≤B.card)
      (hac : a≤c) (hlo : (q:ℝ)^(i+5)*exp (-b)≤(a:ℝ)*c)
      (hhi : (a:ℝ)*c≤2*(q:ℝ)^(i+5)) :
      Description q P (16*H+24*(i:ℝ)+1000) A B a c τ := by
    have low (z : Projectivization (ZMod q) W) x y
        (hg : HeaderOK (Nat.card (ZMod q)) b (i+1) a c
          (projected A z).card (quotientCut B z).card B.card x y) :
        Validated (Nat.card (ZMod q)) P H (i+4) (projected A z) (quotientCut B z) x y (400*τ) := by
      obtain ⟨hx,hy,hxA,hyB,_ha,_hc,hlo',hhi',_hcut⟩ := hg
      have hdq : Module.finrank (ZMod q) (W ⧸ z.submodule)=i+4 := by
        have hh := quotient_dimension z
        omega
      rw [hcard]
      change Validated q (scaleP σ η D R) H (i+4) (projected A z) (quotientCut B z) x y (400*τ)
      apply hs q hq hex (W ⧸ z.submodule) hdq D R had
        (projected A z) (quotientCut B z) x y (b+log 4) (400*τ) hx hy hxA hyB
        (add_nonneg hb hlog4) hb' (by positivity) hτ'
      · simpa only [hcard,show i+1+3=i+4 by omega] using hlo'
      · simpa only [hcard,show i+1+3=i+4 by omega] using hhi'
    have hh := smaller_side_description i hdW σ hσ (by simpa only [hcard] using hex)
      A B a c b τ P H ha hc hac haA hcB hP hH hbP hbσ hτ (by linarith)
      (by simpa only [hcard] using hlo) (by simpa only [hcard] using hhi) low
    simpa only [hcard,Description] using hh
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  have ht' : (0:ℝ)<t := by exact_mod_cast ht
  have hd : 0≤log ((U.card:ℝ)/n) := log_nonneg ((le_div_iff₀ hn').mpr
    (by simpa using (show (n:ℝ)≤U.card by exact_mod_cast hnu)))
  have he : 0≤log ((UT.card:ℝ)/t) := log_nonneg ((le_div_iff₀ ht').mpr
    (by simpa using (show (t:ℝ)≤UT.card by exact_mod_cast htu)))
  have hz : 0≤(q:ℝ)*P*(log ((U.card:ℝ)/n)+log ((UT.card:ℝ)/t)+P) := by positivity
  have hspval (S : Finset (Projectivization (ZMod q) V))
      (T : Finset (Projectivization (ZMod q) (Module.Dual (ZMod q) V)))
      (hsp : (incidenceCount S T:ℝ)≤τ*(n:ℝ)*t/q) :
      (incidenceCount S T:ℝ)≤(n:ℝ)*t/(1000000*Nat.card (ZMod q)) := by
    rw [hcard]
    apply hsp.trans
    have hh := mul_le_mul_of_nonneg_right hsmall (show 0≤(n:ℝ)*t/q by positivity)
    convert hh using 1 <;> ring
  have hd5 : Module.finrank (ZMod q) V=(i+2)+3 := by omega
  by_cases hnt : n≤t
  · obtain ⟨A,hAs,hAc,hAl⟩ := hdesc V hdim U UT n t hn ht hnu htu hnt hplo hphi
    obtain ⟨F,hFs,hFc,hFl⟩ := return_gap_cover hd5 A U UT n t hn ht hnu htu P b (by linarith) hb hbP
      (fun W hW => (hAs W hW).2) (by simpa only [hcard] using hphi)
      (by simpa only [hcard] using hplo)
    refine ⟨F,by simpa only [hcard] using hFs,?_,?_⟩
    · intro S T hSU hSn hTU hTt hsp
      exact hFc S T hSU hSn hTU hTt (hspval S T hsp) (hAc S T hSU hSn hTU hTt hsp)
    · simp only [hcard,Nat.cast_add,Nat.cast_ofNat] at hFl
      dsimp only [P] at *
      nlinarith only [hFl,hAl,hz]
  · have htn : t≤n := le_of_not_ge hnt
    let e := bidual (K:=ZMod q) (V:=V)
    have hcU : (U.image e).card=U.card := card_image_of_injective _ e.injective
    have hddual : Module.finrank (ZMod q) (Module.Dual (ZMod q) V)=i+5 := Subspace.dual_finrank_eq.trans hdim
    obtain ⟨A,hAs,hAc,hAl⟩ := hdesc (Module.Dual (ZMod q) V) hddual UT (U.image e) t n
      ht hn htu (by rwa [hcU]) htn (by simpa only [mul_comm] using hplo) (by simpa only [mul_comm] using hphi)
    obtain ⟨F,hFs,hFc,hFl⟩ := reverse_gap_cover hd5 A U UT n t hn ht hnu htu P (by linarith)
      (fun W hW => (hAs W hW).2) (by simpa only [hcard] using hphi)
    refine ⟨F,by simpa only [hcard] using hFs,?_,?_⟩
    · intro S T hSU hSn hTU hTt hsp
      have hcS : (S.image e).card=n := (card_image_of_injective _ e.injective).trans hSn
      have hinc : incidenceCount T (S.image e)=incidenceCount S T := incidenceCount_bidual S T
      have hspread : (incidenceCount T (S.image e):ℝ)≤τ*(t:ℝ)*n/q := by
        rw [hinc]
        convert hsp using 1; ring
      exact hFc S T hSU hSn hTt (hspval S T hsp)
        (hAc T (S.image e) hTU hTt (image_subset_image hSU) hcS hspread)
    · simp only [hcard,Nat.cast_add,Nat.cast_ofNat] at hFl
      rw [hcU] at hAl
      dsimp only [P] at *
      nlinarith only [hFl,hAl,hz]

theorem uniform_all (i : ℕ) : ∃ H : ℝ,0≤H ∧ Uniform (i+4) H := by
  induction i with
  | zero => exact ⟨7000,by norm_num,uniform_four⟩
  | succ i ih =>
    obtain ⟨H,hH,ih⟩ := ih
    exact ⟨16*H+32*(i:ℝ)+3000,by positivity,uniform_step i H hH ih⟩

end
end SharpLogRamsey.GeometricCover

end

end OAI
