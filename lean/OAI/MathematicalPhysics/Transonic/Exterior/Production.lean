import OAI.MathematicalPhysics.Transonic.Exterior.WindowSound

namespace OAI

section
noncomputable section
namespace SepticProfile.ExteriorCertificates
open FixedInterval ExteriorJet ExteriorJet.NormalizedTrace PowerSeries
open ShootingParameters ExteriorPolynomial

lemma certificate_produces_window {Q : ℤ} (hQ : 0<Q) (boxes : Weights) (tr : Trace)
    (hv : Valid Q 7 73 boxes tr) (hv74 : ValidRow Q 7 74 boxes tr)
    (hn74 : 0<(tr.num 74).center-(tr.num 74).radius)
    {t : ℝ} (ht : t∈Set.Icc leftEnd rightEnd)
    (sig kap : Box) (hs : Holds Q sig (sigma t)) (hk : Holds Q kap (kappa t))
    (ha : WeightsHold Q boxes (1/256) (sigma t) (kappa t) (3/5))
    (h1 : Holds Q (tr.b 1) (slope t/256))
    (hd : ∀ n, 2≤n → n≤73 → Holds Q (tr.den n)
      (2*(1-sigma t)*(slope t/256)*(ratio t-n)))
    (W : WindowData) (hW : WindowValid Q tr sig kap W)
    (u : Series) (hu0 : coeff 0 u=1) (hu1 : coeff 1 u=slope t)
    (he : Formal.residual (sigma t) (kappa t) (3/5) u=0) :
    (∃ d : ℝ, AdmissibleWindow (sigma t) (kappa t) d u) ∧ 0<coeff 74 u := by
  have hb := enclose_source hQ boxes tr hv ht ha h1 hd u hu0 hu1 he
  obtain ⟨d,hpos,hroot,hm⟩ := normalize_window hQ tr sig kap W hW u
    (fun j hj hj' => (hb j hj hj').1) hv.bpos
    (fun j hj hj' => ((hb j (by omega) hj').2 hj).1)
  exact ⟨⟨d,window_sound hQ tr sig kap W hW _ _ d u hs hk hu0 he hpos hroot hm⟩,
    source_coeff74_pos hQ boxes tr hv hv74 hn74 ht ha h1 hd u hu0 hu1 he⟩

end SepticProfile.ExteriorCertificates

end
end

end OAI
