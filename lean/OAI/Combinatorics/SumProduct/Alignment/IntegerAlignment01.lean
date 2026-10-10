import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.RoughArray03
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

noncomputable section
end

noncomputable section
namespace RoughArrayFace
open RationalLattice MalcevCharacters RoughFaceShift RoughTopologicalFace RoughArrayCoordinates
open RoughScales RoughSamplingWeights FinitePieceAverages RoughSourceExceptional RoughProductRemoval
open ProductExposureLabels ProductExposureLaw ProductExposureCutoff MeasureTheory Filter
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable
variable {ι : Type} [Fintype ι] (G : ι→Type) [∀ i,Group (G i)]
variable [∀ i,TopologicalSpace (G i)] [∀ i,IsTopologicalGroup (G i)]
variable (n : ι→ℕ) (q : ℕ) (c : ∀ i,RealCoordinates (G i) (n i))
variable (hsk : ∀ i,SecondKind (c i)) (A : ∀ i,CubeFaces.Filtration (G i))
variable (w : ∀ i,Fin (n i)→ℕ)
variable (hA : ∀ i k (g : G i),g∈(A i).level k ↔ ∀ j,w i j<k → (c i).coord g j=0)
variable (hw : ∀ i j,0<w i j) (Γ : ∀ i,Subgroup (G i))
 

theorem source_raw_physical_array_own_face_decay
    (hΓ : ∀ i g,g∈Γ i ↔ ∀ j,∃ z : ℤ,(c i).coord g j=z)
    [MetricSpace ((Carrier G n q c hsk A w hA)⧸lattice G n q c hsk A w hA Γ)]
    (htop : (inferInstance : MetricSpace
      ((Carrier G n q c hsk A w hA)⧸lattice G n q c hsk A w hA Γ)).toUniformSpace.toTopologicalSpace =
      QuotientGroup.instTopologicalSpace (lattice G n q c hsk A w hA Γ))
    (m v d : ℕ) (hd : 0<d) (c₀ C₀ : ℝ) (B : NNReal) (η : ℝ)
    (hc₀ : 0<c₀) (hC₀ : 0<C₀) (hB : 0<B) (hη : 0<η)
    (w0 M Xp : ℕ→ℕ) (X : ℕ→Fin m→ℕ) (R H : ℕ→ℝ) (L : ℕ→ℤ)
    (hw0 : Tendsto w0 atTop atTop)
    (hX : ∀ N j,4*primorial (w0 N)≤X N j) (hXp : ∀ N,4*primorial (w0 N)≤Xp N)
    (hXt : ∀ j,Tendsto (fun N=>X N j) atTop atTop) (hXpt : Tendsto Xp atTop atTop)
    (hR : ∀ N,0<R N) (hRX : Tendsto (fun N=>R N/(Xp N:ℝ)) atTop (𝓝 0))
    (hZ : ∀ a : ℝ,0<a →Tendsto (fun N=>(R N/(M N:ℝ))/
      (1+∑ j,(X N j:ℝ)^2)^a) atTop atTop)
    (hH : ∀ N,0≤H N) (hHZ : Tendsto (fun N=>H N/(R N/(M N:ℝ))) atTop (𝓝 0))
    (hWM : ∀ N,(primorial (w0 N):ℤ)∣(M N:ℤ))
    (hM : ∀ N,0<M N) (hMs : ∀ N,Smooth (w0 N) (M N:ℤ))
    (hL : ∀ N,0<L N) (hsm : ∀ N,Smooth (w0 N) (L N))
    (hWL : ∀ N,(primorial (w0 N):ℤ)∣L N)
    (hML : ∀ N,(M N:ℤ)∣L N)
    (hXL : ∀ j,Tendsto (fun N=>(X N j:ℝ)/(L N:ℝ)) atTop atTop)
    (pattern : ι→Fin (v+1)→ℤ) (e : Fin q) (j : Fin (v+1))
    (g x : ℕ→Label m→∀ i,G i) (b0 b1 : ℕ→Label m→ι→ℝ)
    (a0 a1 : ℕ→Label m→Fin q→ℝ)
    (δ : ℕ→Label m→(Fin m→ℤ)→ℤ)
    (hδ : ∀ N b,b∈(fullDomain (X N) (Xp N) (primorial (w0 N))).image
      (expose (L N) (M N:ℤ) (R N)) → Good (X N) (Xp N) (R N) b →
      ∀ t∈productTimes b.scales b.residue (L N),
        (δ N b t:ℝ)=a0 N b e+a1 N b e*∏ l,(t l:ℝ) ∧
        (d:ℤ)∣δ N b t ∧ |(δ N b t:ℝ)|≤H N) :
    Tendsto (fun N=>(jointLaw (X N) (Xp N) (primorial (w0 N)) (primorial_pos _)
      (hX N) (hXp N)).real (rawPhysicalEvent (lattice G n q c hsk A w hA Γ) m v c₀ C₀ B η (R N) d (M N) (L N)
        (fun b=>actualData G n q c hsk A w hA hw Γ pattern (g N b) (x N b)
          (b0 N b) (b1 N b) (a0 N b) (a1 N b) e j (coarseOrigin v (M N) (R N) b) (δ N b))))
      atTop (𝓝 0)
 := by
  let C' : ℝ:=(2:ℝ)^m+2+C₀*2^m
  let F : ℕ→Label m→FaceData m (v+1) (Carrier G n q c hsk A w hA)
      (lattice G n q c hsk A w hA Γ) := fun N b=>
    actualData G n q c hsk A w hA hw Γ pattern (g N b) (x N b)
      (b0 N b) (b1 N b) (a0 N b) (a1 N b) e j (coarseOrigin v (M N) (R N) b) (δ N b)
  have hC' : 0<C' := by dsimp [C'];positivity
  have hraw:=source_raw_array_own_face_decay G n q c hsk A w hA hw Γ hΓ htop
    m (v+1) d hd c₀ C' B η hc₀ hC' hB hη w0 M Xp X R H L hw0 hX hXp hXt hXpt
    hR hRX hZ hH hHZ hWM hM hMs hL hsm hWL hXL pattern e j g x b0 b1 a0 a1
    (fun N b=>coarseOrigin v (M N) (R N) b) δ hδ
  have hMr (N : ℕ) : (0:ℝ)<M N := by exact_mod_cast hM N
  have hZtop : Tendsto (fun N=>R N/(M N:ℝ)) atTop atTop := by
    apply tendsto_atTop_mono (fun N=>?_) (hZ 1 (by norm_num))
    rw [Real.rpow_one]
    exact div_le_self (div_nonneg (hR N).le (hMr N).le)
      (by have:=Finset.sum_nonneg (fun j (_ : j∈Finset.univ)=>sq_nonneg (X N j:ℝ));linarith)
  apply squeeze_zero' (Eventually.of_forall (fun _=>measureReal_nonneg)) ?_ hraw
  filter_upwards [hw0.eventually (eventually_ge_atTop d),hZtop.eventually (eventually_ge_atTop 1)]
    with N hdw hRM
  change (jointLaw (X N) (Xp N) (primorial (w0 N)) (primorial_pos _) (hX N) (hXp N)).real
    (rawPhysicalEvent (lattice G n q c hsk A w hA Γ) m v c₀ C₀ B η (R N) d (M N) (L N) (F N))≤_
  rw [←joint_restrict_fullDomain (X N) (Xp N) (primorial (w0 N)) (primorial_pos _) (hX N) (hXp N)]
  refine measureReal_mono ?_ (by finiteness)
  exact rawPhysical_subset (lattice G n q c hsk A w hA Γ) m v (w0 N) (M N) d hd hdw
    (X N) (Xp N) (fun l=>by have:=hX N l;have:=primorial_pos (w0 N);omega)
    (hM N) (hMs N) (R N) (hR N) hRM (L N) (hML N) c₀ C₀ hc₀.le hC₀.le B η (F N)
    (fun _=>rfl)

end RoughArrayFace
end

 

open scoped BigOperators
namespace IntegerAlignment

 
lemma fixed_dvd_primorial_pow {n w k : ℕ} (hn : 0 < n) (hnw : n ≤ w) (hnk : n ≤ k) :
    n ∣ primorial w ^ k := by
  have hW : primorial w ≠ 0 := (primorial_pos w).ne'
  have h : n ∣ primorial w ^ n := by
    apply (Nat.dvd_pow_self_iff hn.ne' hW).mpr
    intro p hp
    obtain ⟨hpp,hpn,_⟩ := Nat.mem_primeFactors.mp hp
    exact Nat.mem_primeFactors.mpr ⟨hpp,
      hpp.dvd_primorial_iff.mpr ((Nat.le_of_dvd hn hpn).trans hnw),hW⟩
  exact h.trans (pow_dvd_pow _ hnk)

 
lemma fixed_mul_primorial_dvd {n w : ℕ} (hn : 0 < n) (hw : n + 1 ≤ w) :
    n * primorial w ∣ primorial w ^ w := by
  have h := fixed_dvd_primorial_pow hn (by omega : n ≤ w) (by omega : n ≤ w - 1)
  have h' := mul_dvd_mul_right h (primorial w)
  simpa [← pow_succ, show w - 1 + 1 = w by omega] using h'

 
lemma finite_absorption (S : Finset ℕ) (hS : ∀ n ∈ S, 0 < n) :
    ∃ w₀ : ℕ, ∀ w ≥ w₀, ∀ n ∈ S, n * primorial w ∣ primorial w ^ w := by
  refine ⟨S.sup id + 1,?_⟩
  intro w hw n hn
  exact fixed_mul_primorial_dvd (hS n hn) (by
    have := Finset.le_sup (f := id) hn
    simp only [id_eq] at this
    omega)

def Smooth (w : ℕ) (b : ℤ) : Prop := ∀ p : ℕ, p.Prime → (p : ℤ) ∣ b → p ≤ w

def Rough (w : ℕ) (t : ℤ) : Prop := ∀ p : ℕ, p.Prime → p ≤ w → ¬ (p : ℤ) ∣ t

lemma coprime_smooth_rough {w : ℕ} {b t : ℤ} (hb : Smooth w b) (ht : Rough w t) :
    IsCoprime b t := by
  rw [Int.isCoprime_iff_nat_coprime]
  apply Nat.coprime_of_dvd
  intro p hp hpb hpt
  exact ht p hp (hb p hp (Int.natCast_dvd.mpr hpb)) (Int.natCast_dvd.mpr hpt)

lemma primorial_smooth (w : ℕ) : Smooth w (primorial w : ℤ) := by
  intro p hp hpd
  exact hp.dvd_primorial_iff.mp (by exact_mod_cast hpd)

lemma coprime_modulus {w : ℕ} {M t : ℤ} (hM : Smooth w M) (ht : Rough w t) :
    IsCoprime t (M * (primorial w : ℤ) ^ w) := by
  exact (coprime_smooth_rough hM ht).symm.mul_right
    (coprime_smooth_rough (primorial_smooth w) ht).symm.pow_right

 
lemma integral_translation {q₀ W H a : ℤ} (hq₀ : q₀ ≠ 0)
    (hH : q₀ * W ∣ H) :
    ∃ q : ℤ, (q : ℚ) = (H : ℚ) / q₀ * a ∧ W ∣ q := by
  obtain ⟨b, rfl⟩ := hH
  refine ⟨W * b * a,?_,dvd_mul_of_dvd_left (dvd_mul_right W b) a⟩
  have hq : (q₀ : ℚ) ≠ 0 := by exact_mod_cast hq₀
  push_cast
  field_simp

 

lemma residue_shift {M W t q : ℤ} {w : ℕ} (hM : 0 < M) (hW : 0 < W)
    (hw : 1 ≤ w) (ht : IsCoprime t (M * W ^ w)) (hq : W ∣ q) :
    ∃ r Δ : ℤ, 0 ≤ r ∧ r < M * W ^ w ∧
      t * r ≡ q [ZMOD M * W ^ w] ∧
      Δ = (q - t * r) / M ∧ W ∣ r ∧ W ^ w ∣ Δ ∧
      ∀ p m : ℤ, t * (p + m * r) + m * M * Δ = t * p + m * q := by
  let L := M * W ^ w
  have hL : 0 < L := mul_pos hM (pow_pos hW w)
  obtain ⟨a,b,hab⟩ := ht
  let r := (a * q) % L
  have hc : t * r ≡ q [ZMOD L] := by
    have h₁ : t * r ≡ t * (a * q) [ZMOD L] := (Int.mod_modEq _ _).mul_left t
    apply h₁.trans
    rw [Int.modEq_iff_dvd]
    refine ⟨b * q,?_⟩
    change q - t * (a * q) = M * W ^ w * (b * q)
    nlinarith [congrArg (fun x : ℤ => x * q) hab]
  obtain ⟨k,hk⟩ := Int.modEq_iff_dvd.mp hc
  have hWL : W ∣ L := (dvd_pow_self W (by omega : w ≠ 0)).trans (dvd_mul_left _ M)
  have hWt : IsCoprime W t := (IsCoprime.of_isCoprime_of_dvd_right
    (show IsCoprime t L from ⟨a,b,hab⟩) hWL).symm
  have hWr : W ∣ r := by
    apply hWt.dvd_of_dvd_mul_left
    have hd : W ∣ q - t * r := hWL.trans (Int.modEq_iff_dvd.mp hc)
    have := dvd_sub hq hd
    simpa using this
  refine ⟨r,W ^ w * k,Int.emod_nonneg _ hL.ne',Int.emod_lt_of_pos _ hL,
    hc,?_,hWr,dvd_mul_right _ k,?_⟩
  · rw [hk]
    change W ^ w * k = M * W ^ w * k / M
    rw [mul_assoc,Int.mul_ediv_cancel_left _ hM.ne']
  · intro p m
    change q - t * r = M * W ^ w * k at hk
    nlinarith [congrArg (fun x : ℤ => m * x) hk]

 
lemma residue_unique {L t q r r' : ℤ} (_hL : 0 < L) (ht : IsCoprime t L)
    (hr : 0 ≤ r) (hrL : r < L) (hr' : 0 ≤ r') (hrL' : r' < L)
    (hc : t * r ≡ q [ZMOD L]) (hc' : t * r' ≡ q [ZMOD L]) : r = r' := by
  have hd : L ∣ r' - r := by
    apply ht.symm.dvd_of_dvd_mul_left
    simpa only [mul_sub] using Int.modEq_iff_dvd.mp (hc.trans hc'.symm)
  have hm := Int.modEq_iff_dvd.mpr hd
  change r % L = r' % L at hm
  simpa only [Int.emod_eq_of_lt hr hrL,Int.emod_eq_of_lt hr' hrL'] using hm

 

lemma own_target_reading {E : Type*} (S : Finset E) (t p : ℤ)
    (r Δ q m v : E → ℤ) (M : ℤ)
    (hid : ∀ e ∈ S, q e - t * r e = M * Δ e) :
    t * (p + ∑ e ∈ S, v e * r e + ∑ e ∈ S, m e * r e) +
        M * ∑ e ∈ S, m e * Δ e =
      t * (p + ∑ e ∈ S, v e * r e) + ∑ e ∈ S, m e * q e := by
  have hs : ∑ e ∈ S, m e * q e =
      t * ∑ e ∈ S, m e * r e + M * ∑ e ∈ S, m e * Δ e := by
    rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e he
    nlinarith [congrArg (fun x : ℤ => m e * x) (hid e he)]
  rw [hs]
  ring

 

lemma terminal_translation {q₀ hA hB bA bB dA dB tA : ℚ} {m q : ℤ}
    (hq₀ : q₀ ≠ 0) (hB0 : hB ≠ 0) (hbB : bB ≠ 0) (hdB : dB ≠ 0)
    (hm : (m : ℚ) = q₀ * (bA / bB) * (dA / dB))
    (hq : (q : ℚ) = (hA / (q₀ * hB)) * tA) :
    ((m * q : ℤ) : ℚ) = (hA * bA * dA / (hB * bB * dB)) * tA := by
  push_cast
  rw [hm,hq]
  field_simp

 

structure ResidueData (q₀ M W H a t : ℤ) (w : ℕ) where
  q : ℤ
  r : ℤ
  Δ : ℤ
  q_value : (q : ℚ) = (H : ℚ) / q₀ * a
  r_nonneg : 0 ≤ r
  r_lt : r < M * W ^ w
  congruence : t * r ≡ q [ZMOD M * W ^ w]
  Δ_value : Δ = (q - t * r) / M
  W_dvd_q : W ∣ q
  W_dvd_r : W ∣ r
  pow_dvd_Δ : W ^ w ∣ Δ
  identity : ∀ p m : ℤ, t * (p + m * r) + m * M * Δ = t * p + m * q

 

theorem residue_system {E : Type*} (q₀ w : ℕ) (hq₀ : 0 < q₀) (hw : q₀ + 1 ≤ w)
    (M : ℤ) (hM : 0 < M) (hSM : Smooth w M)
    (H a t : E → ℤ) (hH : ∀ e, (primorial w : ℤ) ^ w ∣ H e)
    (ht : ∀ e, Rough w (t e)) :
    Nonempty (∀ e, ResidueData q₀ M (primorial w) (H e) (a e) (t e) w) := by
  classical
  have hbase : (q₀ : ℤ) * (primorial w : ℤ) ∣ (primorial w : ℤ) ^ w := by
    exact_mod_cast fixed_mul_primorial_dvd hq₀ hw
  have hq0 : (q₀ : ℤ) ≠ 0 := by exact_mod_cast hq₀.ne'
  have hW : (0 : ℤ) < primorial w := by exact_mod_cast primorial_pos w
  have hdata : ∀ e, Nonempty (ResidueData q₀ M (primorial w) (H e) (a e) (t e) w) := by
    intro e
    obtain ⟨q,hq,hqd⟩ := integral_translation hq0 (hbase.trans (hH e)) (a := a e)
    obtain ⟨r,Δ,h0,hr,hc,hΔ,hrd,hΔd,hid⟩ :=
      residue_shift hM hW (by omega : 1 ≤ w) (coprime_modulus hSM (ht e)) hqd
    exact ⟨⟨q,r,Δ,hq,h0,hr,hc,hΔ,hqd,hrd,hΔd,hid⟩⟩
  exact ⟨fun e => Classical.choice (hdata e)⟩

lemma fixed_dvd_delta {q₀ M H a t : ℤ} {w n : ℕ}
    (D : ResidueData q₀ M (primorial w) H a t w) (hn : 0 < n) (hnw : n ≤ w) :
    (n : ℤ) ∣ D.Δ := by
  have h : (n : ℤ) ∣ (primorial w : ℤ) ^ w := by
    exact_mod_cast fixed_dvd_primorial_pow hn hnw hnw
  exact h.trans D.pow_dvd_Δ

 
lemma rough_slot {E : Type*} (S : Finset E) (v r : E → ℤ) {w : ℕ} {p : ℤ}
    (hp : Rough w p) (hr : ∀ e ∈ S, (primorial w : ℤ) ∣ r e) :
    Rough w (p + ∑ e ∈ S, v e * r e) := by
  have hs : (primorial w : ℤ) ∣ ∑ e ∈ S, v e * r e :=
    Finset.dvd_sum (fun e he => dvd_mul_of_dvd_right (hr e he) (v e))
  intro ℓ hℓ hℓw hd
  have hℓW : (ℓ : ℤ) ∣ (primorial w : ℤ) := by
    exact_mod_cast hℓ.dvd_primorial_iff.mpr hℓw
  have : (ℓ : ℤ) ∣ p := by
    simpa using dvd_sub hd (hℓW.trans hs)
  exact hp ℓ hℓ hℓw this

 

lemma model_array_exponent {G : Type*} [Group G] (g : G) (n M d : ℤ) (hM : M ≠ 0) :
    g ^ ((n + M * d - (n + M * d) % M) / M) =
      g ^ ((n - n % M) / M) * g ^ d := by
  have hmod : (n + M * d) % M = n % M := Int.add_mul_emod_self_left n M d
  rw [hmod]
  have he : (n + M * d - n % M) / M = (n - n % M) / M + d := by
    rw [show n + M * d - n % M = (n - n % M) + d * M by ring]
    exact Int.add_mul_ediv_right _ _ hM
  rw [he,zpow_add]

end IntegerAlignment


end OAI
