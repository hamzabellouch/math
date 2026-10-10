import Mathlib
import OAI.Combinatorics.RamseyFive.Marking.ClassifiedStream
import OAI.Combinatorics.RamseyFive.Marking.ReciprocalSharpRound
import OAI.Combinatorics.RamseyFive.Marking.ReciprocalStageArithmetic
import OAI.Combinatorics.RamseyFive.Entropy.ReciprocalCodeNumerics
import OAI.Combinatorics.RamseyFive.Entropy.ReciprocalLossBudget
import OAI.Combinatorics.RamseyFive.Marking.BandEndpoints

namespace OAI

namespace SharpRamseyFive.SelectedTuple
open Module ProjectiveIncidence FiniteEntropy Windows Marking Filter ParameterHierarchy
open scoped Classical BigOperators LinearAlgebra.Projectivization NNReal
noncomputable section

theorem eventually_forward_prepared_stage {η : ℝ} (hη : 0<η) (hη' : η<1/10)
    (c C Cm : ℝ) (hc : 0<c) (hC : 0≤C) (hCm : 0≤Cm) :
    ∀ᶠ σ : ℝ in atTop,∀ (q₀ : ℕ) (K V Ω κ α : Type) [Field K] [AddCommGroup V] [Module K V]
      [Finite K] [CharP K q₀] [FiniteDimensional K V]
      [Fintype (ℙ K V)] [Fintype (ℙ K (Dual K V))]
      [Fintype (ℙ K (Dual K (Dual K V)))] [Fintype Ω] [Fintype κ] [Fintype α],
    ∀ (N m l : ℕ) (admissible : (Fin N→α)→Prop)
      (S : SelectedStream (Ω:=Ω) (β:=FlagPair K V) N m admissible)
      (ctx : Ω→κ) (D B M k₀ : ℝ)
      (PS : Prepared S ctx (Real.log (153*(Nat.card K:ℝ)^4)) B M) (b : Fin 7),
      finrank K V=5→3≤Nat.card K→Nat.card K=q₀→1≤σ→Real.exp σ=Nat.card K→
      σ^beta η≤D→D≤σ^(1-η/2)→c*(Nat.card K:ℝ)*σ^(1+η)≤ m→
      (m:ℝ)≤(Nat.card K:ℝ)*σ^(1+η)→(l:ℝ)≤ m/100→
      (Nat.card K:ℝ)*σ^(1+η)≤2*k₀→0≤B→B≤C*m*D*σ^(-beta η)→0≤M→M≤Cm*σ→
      (∀a,0 < map S.law ctx a→∀i,DomainClass (D*σ^(3*beta η)) (PS.domain a i) (.inl b))→
      Nonempty (CodedStream (K:=K) (V:=V) N l admissible ((10/9)*S.density)
        (k₀*D*σ^(-η/3)) (Real.log (153*(Nat.card K:ℝ)^4)+domainSlackConstant*D*σ^(6*beta η)) M) := by
  have hCb : 0≤3+Real.log 4 := by have:=Real.log_nonneg (show (1:ℝ)≤4 by norm_num);linarith
  filter_upwards [eventually_reciprocal_coded_stage hη hη' (3+Real.log 4) 153 (1/10000) hCb (by norm_num) (by norm_num),
    eventually_reciprocal_packing hη hη' c hc,eventually_reciprocal_local_numbers hη,
    eventually_public_integers (beta_pos hη),eventually_reciprocal_code_budget hη hη',
    eventually_reciprocal_loss_budget hη c C Cm hc hC hCm,
    eventually_reciprocal_endpoints (beta_pos hη) 153 (1/2) (by norm_num) (by norm_num)]
    with σ hstage hpack hlocal hpublic hcode hloss hend
  intro q₀ K V Ω κ α _ _ _ _ _ _ _ _ _ _ _ _ N m l adm S ctx D B M k₀ PS b
    hd hq3 hcard hσ hq hD hDhi hlen hm hl hk₀ hB hBhi hM hMhi hcl
  have hp : 0<σ := zero_lt_one.trans_le hσ
  have hqp : (0:ℝ)<Nat.card K := by rw [←hq];positivity
  have hqr : (2:ℝ)≤Nat.card K := by exact_mod_cast (show 2≤Nat.card K by omega)
  have hDp : 0<D := (Real.rpow_pos_of_pos hp _).trans_le hD
  have hσeq : Real.log (Nat.card K)=σ := by rw [←hq,Real.log_exp]
  have hJ : Real.log (153*(Nat.card K:ℝ)^4)=Real.log 153+4*σ := by
    rw [Real.log_mul (by norm_num) (pow_pos hqp _).ne',Real.log_pow,hσeq];norm_num
  have hlog153 : 0≤Real.log 153 := Real.log_nonneg (by norm_num)
  let closed : Bool:=decide (b.val%2=0)
  obtain ⟨w,n,T,rem,hw,hn,hpacking,hml,hwD,hw2,hclosed,hopen,hT,hr,hnr,hroom,hTlo,hrlo⟩:=
    hpack (Nat.card K) D m hqr hD hDhi hlen hm closed
  let : Nonempty (Fin n):=⟨⟨0,hn⟩⟩
  let R:=⌈σ^beta η⌉₊
  let H:=⌈σ^(beta η/2)⌉₊
  obtain ⟨hHpos,hwH,hHhi,hRlo,hRhi⟩:=hpublic w hw2
  have hRange : Range η σ D R := ⟨hD,hDhi,hRlo,hRhi⟩
  let L₀ : ℝ≥0:=⟨L η σ D,by unfold L;positivity⟩
  let e:=Fin.castLEOrderEmb hpacking
  let S':=S.reindex e
  let PS':=PS.reindex e
  let u : κ→Slots w n→ℝ:=fun c i=>if h : 0 < map S.law ctx c then
    (hcl c h (e (slotEmbedding i))).choose else 0
  have hu : ∀c,0 < map S'.law ctx c→∀i,
      σ≤u c i ∧ u c i≤4*σ ∧ ForwardCaps (PS'.domain c (slotEmbedding i)) (u c i) ∧
        BandCondition σ (D*σ^(3*beta η)) (u c i) b := by
    intro c hc i
    change 0 < map S.law ctx c at hc
    have hh:=(hcl c hc (e (slotEmbedding i))).choose_spec
    simpa only [u,dite_eq_left hc,hσeq,PS',Prepared.reindex] using hh
  have hflag : ∀c,0 < map S'.law ctx c→∀i,
      ((PS'.domain c (slotEmbedding i)).card:ℝ)≤153*(Nat.card K:ℝ)^4 := by
    intro c hc i
    exact card_le_of_log_le (by positivity) (by positivity) (PS'.cap c (slotEmbedding i))
  have hlwn : (l:ℝ)≤(w:ℝ)*n := by nlinarith
  have hlmid : l<w*(2*n) := by
    have hpos : (0:ℝ)<(w:ℝ)*n := by positivity
    exact_mod_cast (show (l:ℝ)<(w:ℝ)*(2*n) by nlinarith)
  have hll : (l:ℝ)≤(Nat.card K:ℝ)*σ^(1+η) := by
    have hm0 : (0:ℝ)≤ m := by positivity
    linarith
  obtain ⟨hs,hsmall,hwide,hkb0,hkbhi,hε⟩:=hlocal D hD hDhi
  obtain ⟨hmass,hcore⟩:=hend D hD
  have hnum:=hloss (Nat.card K) D m w n B T rem M
    (bandHi σ (D*σ^(3*beta η)) b-bandLo σ (D*σ^(3*beta η)) b) l
    hqp hD (by exact_mod_cast hw) (by exact_mod_cast hn) hml hB hBhi hTlo hrlo hM hMhi hlwn
    closed hclosed hopen (by
      intro hh
      have hb : b.val%2=0 := by simpa only [closed,decide_eq_true_eq] using hh
      rw [band_gap_closed hb];ring_nf;exact le_rfl)
    (by
      intro hh
      have hb : b.val%2≠0 := by simpa only [closed,decide_eq_false_iff_not] using hh
      rw [band_gap_open hb])
  obtain ⟨out⟩:=hstage D (D*σ^(6*beta η)) (Real.log (153*(Nat.card K:ℝ)^4))
    (bandLo σ (D*σ^(3*beta η)) b) (bandHi σ (D*σ^(3*beta η)) b) B M (D*σ^(3*beta η)) R L₀
    q₀ K V Ω κ α hd hq3 N w n H T rem l adm S' ctx PS' u b
    (fun c hc i=>(hu c hc i).2.2.1) hflag
    (fun c hc i=>band_endpoints hp.le (by positivity) ⟨(hu c hc i).1,(hu c hc i).2.1⟩ (hu c hc i).2.2.2)
    (by simpa only [hσeq] using (fun c hc i=>(hu c hc i).2.2.2))
    (band_lo_le_hi hp.le (by positivity)) (by positivity) (by rw [hσeq,hJ];linarith)
    hσ hq hcard hRange rfl hT hr hnr hroom hlmid hM hs
    (by simpa only [hσeq] using hsmall) hwide hkb0 hkbhi hwH hHhi hmass
    (by simpa only [hσeq] using hcore) (by simpa only [hq] using hε) (by
      simpa only [closed,decide_eq_true_eq,Nat.cast_mul,Nat.cast_ofNat,hq,show (4:ℝ)*(w*(4*n))=16*w*n by ring] using hnum)
  refine ⟨out.mono le_rfl (hcode (Nat.card K) D R k₀ w H l hq hRange hHpos hHhi hwD hk₀ hll) ?_⟩
  have hh:=reciprocal_domain_slack_bound hη hσ hD
  rw [hJ]
  linarith
end
end SharpRamseyFive.SelectedTuple

end OAI
