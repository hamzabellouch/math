import OAI.Analysis.MutuallyUnbiased.MixedTargets.KeyTable

namespace OAI

namespace MUB6.Certificate.MixedTargetSemantics

def keyPolynomialBlock79 : Integer.Sparse (Fin 2886) := [(2528, -64673782080), (2529, 31184084640), (2530, 52916319280), (2531, -55902749040), (2532, 22565850336), (2533, -40363279680), (2534, -82919052640), (2535, -55872858880), (2536, 118038269760), (2537, 72946361760), (2538, 76682450400), (2539, 176570546880), (2540, 4171087840), (2541, 84249384000), (2542, -18685629280), (2543, -17400605280), (2544, -118378819600), (2545, 74745834480), (2546, 10849510160), (2547, 93928209840), (2548, 167739810240), (2549, 40021870200), (2550, 248493837600), (2551, 35303490240), (2552, 97921657320), (2553, 56559228480), (2554, 134217930960), (2555, 1828358280), (2556, 39516772800), (2557, 4773588640), (2558, -100814408880), (2559, 73844861120)]

def originalBlock79 : Integer.Sparse OriginalKey := [(Sum.inl 2661, 39516772800), (Sum.inl 2662, -40363279680), (Sum.inl 2673, 84249384000), (Sum.inl 2677, 35303490240), (Sum.inl 2678, -64673782080), (Sum.inl 2687, 72946361760), (Sum.inl 3038, 167739810240), (Sum.inl 3055, 118038269760), (Sum.inl 3223, 73844861120), (Sum.inl 3224, 93928209840), (Sum.inl 3524, -17400605280), (Sum.inl 3538, 4171087840), (Sum.inl 3570, 176570546880), (Sum.inl 3832, 10849510160), (Sum.inl 3833, 1828358280), (Sum.inl 3834, 156783781296), (Sum.inl 3840, 61332817120), (Sum.inl 3841, 97921657320), (Sum.inl 3854, 248493837600), (Sum.inl 3855, -100814408880), (Sum.inl 3856, 40021870200), (Sum.inl 3870, -55902749040), (Sum.inl 3871, 52916319280), (Sum.inl 3872, 31184084640), (Sum.inl 3873, -118378819600), (Sum.inl 3874, 74745834480), (Sum.inl 3877, 76682450400), (Sum.inl 3880, -82919052640), (Sum.inl 3882, -55872858880), (Sum.inl 3884, -18685629280), (Sum.inl 4889, 295379444480), (Sum.inl 4898, 375712839360), (Sum.inl 5184, -69602421120), (Sum.inl 5188, 16684351360), (Sum.inl 5198, 706282187520), (Sum.inl 5206, 291785447040), (Sum.inl 5219, 158067091200), (Sum.inl 5220, -161453118720), (Sum.inl 5229, 336997536000), (Sum.inl 5232, 141213960960), (Sum.inl 5233, -258695128320), (Sum.inl 5267, 670959240960), (Sum.inl 5300, 472153079040), (Sum.inl 5376, 7313433120), (Sum.inl 5379, 43398040640), (Sum.inl 5381, 627135125184), (Sum.inl 5412, 160087480800), (Sum.inl 5420, -223610996160), (Sum.inl 5421, -473515278400), (Sum.inl 5425, 370067607040), (Sum.inl 5426, 391686629280), (Sum.inl 5429, 298983337920), (Sum.inl 5430, 211665277120), (Sum.inl 5436, 1300705152000), (Sum.inl 5437, -403257635520), (Sum.inl 5445, -331676210560), (Sum.inl 5446, -74742517120), (Sum.inl 5447, -223491435520)]

theorem originalBlockCheck79 : originalBlock79 =
    Integer.Sparse.collectBalanced originalLess (Integer.Sparse.substitute keyPolynomialBlock79 keyMomentRows) := by decide +kernel

theorem originalBlockEval79 (x : OriginalKey → ℝ) :
    Integer.Sparse.eval originalBlock79 x =
      Integer.Sparse.eval keyPolynomialBlock79 (fun i => Integer.Sparse.eval (keyMomentRows i) x) := by
  rw [originalBlockCheck79, Integer.Sparse.eval_collectBalanced, Integer.Sparse.eval_substitute]

end MUB6.Certificate.MixedTargetSemantics

end OAI
